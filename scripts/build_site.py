#!/usr/bin/env python3
"""Build the offline research site from blueprint JSON and exported Lean metadata.

Run from any directory: python3 scripts/build_site.py [--without-pdf] [--node PATH].
No network or package installation is performed. Missing declaration metadata,
ambiguous source positions, invalid TeX, and broken local links are fatal.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import shutil
import subprocess
import sys
import textwrap
import unicodedata
from collections import defaultdict
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "website-template"
OUT = ROOT / "website"
AUTHORS = {"en": "GPT-6 Astra · Juii-hang Leung",
           "zh-CN": "GPT-6 Astra · Juii-hang Leung（龙维汉）"}
LOCALES = ("en", "zh-CN")
UI = None


def esc(value):
    return html.escape(str(value), quote=True)


def fail(message):
    raise ValueError(message)


def read_json(path):
    if not path.is_file():
        fail(f"Required input is missing: {path.relative_to(ROOT)}")
    return json.loads(path.read_text(encoding="utf-8"))


def anchor(name):
    return "decl-" + name


def declaration_url(name):
    return "declarations.html#" + quote(anchor(name), safe="")


def source_url(file, line=None):
    return "source/" + quote(file, safe="/") + ".html" + (f"#L{line}" if line else "")


def paragraphs(value):
    return "".join(f"<p>{esc(p)}</p>" for p in str(value).split("\n\n") if p.strip())


def listing(items):
    return "<ul>" + "".join(f"<li>{esc(x)}</li>" for x in items) + "</ul>"


def external_link(url, title):
    if urlsplit(url).scheme not in {"https", "http"}:
        fail(f"Unsupported reference URL: {url}")
    return f'<a href="{esc(url)}">{esc(title)}</a>'


def page(title, body, filename, section, lang, css_class=""):
    ui = UI[lang]
    prefix = "../" * (len(Path(filename).parts) - 1)
    nav = []
    for key, label, target in [("index", ui["overview"], "index.html"),
                               ("blueprint", ui["blueprint"], "blueprint.html"),
                               ("declarations", ui["declarations"], "declarations.html"),
                               ("sources", ui["sources"], "sources.html")]:
        current = ' aria-current="page"' if key == section else ""
        nav.append(f'<a href="{prefix}{target}"{current}>{esc(label)}</a>')
    result = (TEMPLATE / "page.html").read_text(encoding="utf-8")
    site_root = prefix + ("../" if lang == "zh-CN" else "")
    locale, subdir = ("zh-CN", "zh/") if lang == "en" else ("en", "")
    label = ui["switch_language"]
    switch = (f'<a class="language-switch" data-language-switch="{locale}" hreflang="{locale}" '
              f'aria-label="{esc(label)}" title="{esc(label)}" '
              f'href="{site_root}{subdir}{quote(filename, safe="/")}">'
              '<svg class="globe" viewBox="0 0 24 24" aria-hidden="true" focusable="false">'
              '<circle cx="12" cy="12" r="9"/><ellipse cx="12" cy="12" rx="4" ry="9"/>'
              '<path d="M3 12h18M5 6.5h14M5 17.5h14"/></svg>'
              f'<span class="language-label">{esc(ui["language_label"])}</span></a>')
    for key, value in {"TITLE": esc(title), "ROOT": site_root, "LOCAL_ROOT": prefix, "NAV": "".join(nav),
                       "CLASS": esc(css_class), "BODY": body, "LANG": lang,
                       "LANG_SWITCH": switch, "DESCRIPTION": esc(ui["description"]),
                       "SITE_TITLE": esc(ui["site_title"]), "SKIP": esc(ui["skip"]),
                       "NAV_LABEL": esc(ui["navigation"])}.items():
        result = result.replace("@@" + key + "@@", value)
    if re.search(r"@@[A-Z]+@@", result):
        fail(f"Unfilled template token in {filename}")
    return result


def load_inputs():
    blueprint_path = ROOT / "blueprint/blueprint.json"
    metadata_path = ROOT / "verification/blueprint-declarations.json"
    bp = read_json(blueprint_path)
    md = read_json(metadata_path)
    nodes = bp.get("nodes")
    records = md.get("records")
    if not isinstance(nodes, list) or not nodes:
        fail("Blueprint nodes must be a nonempty list.")
    if not isinstance(records, list) or not records:
        fail("Exported metadata records must be a nonempty list; types will not be inferred or fabricated.")
    ids = [n["id"] for n in nodes]
    if len(set(ids)) != len(ids) or any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", x) for x in ids):
        fail("Blueprint node IDs must be unique, safe HTML identifiers.")
    expected = {}
    for node in nodes:
        if not isinstance(node.get("math_statement"), str):
            fail(f"Missing math_statement: {node['id']}")
        for dep in node.get("dependencies", []):
            if dep not in ids:
                fail(f"Unknown prerequisite {dep} for {node['id']}")
        for group in node.get("lean", []):
            for name in group.get("declarations", []):
                if name in expected and expected[name] != group["file"]:
                    fail(f"Conflicting source files for {name}")
                expected[name] = group["file"]
    sources = {str(p.relative_to(ROOT)): p.read_text(encoding="utf-8")
               for p in sorted((ROOT / "CurveControl").rglob("*.lean"))}
    if (ROOT / "CurveControl.lean").is_file():
        sources["CurveControl.lean"] = (ROOT / "CurveControl.lean").read_text(encoding="utf-8")
    indexed = {}
    for original in records:
        record = dict(original)
        name, signature = record.get("declaration"), record.get("type")
        if not isinstance(name, str) or not isinstance(signature, str) or not signature.strip():
            fail("Every exported record must have a declaration and a nonempty real Lean type.")
        if "⋯" in signature:
            fail(f"Truncated Lean type contains ⋯: {name}. Export the complete type before building.")
        if name in indexed:
            fail(f"Duplicate exported declaration: {name}")
        file = record.get("file") or expected.get(name)
        if file:
            candidate = Path(file)
            if candidate.is_absolute():
                try:
                    file = str(candidate.resolve().relative_to(ROOT))
                except ValueError:
                    fail(f"Source is outside this project: {name}: {file}")
            file = Path(file).as_posix()
        if file not in sources:
            fail(f"Missing project source file for {name}: {file!r}")
        lines = sources[file].splitlines()
        line = record.get("line")
        if line is not None:
            if not isinstance(line, int) or isinstance(line, bool) or not 1 <= line <= len(lines):
                fail(f"Invalid source line for {name}: {line!r}")
        else:
            leaf = name.rsplit(".", 1)[-1]
            pattern = re.compile(r"\b(?:theorem|lemma|def|abbrev|structure|class|instance)\s+"
                                 r"(?:[\w'.]+\.)?" + re.escape(leaf) + r"(?=[\s:({\[⦃]|$)")
            hits = [i for i, text in enumerate(lines, 1) if pattern.search(text)]
            if len(hits) != 1:
                fail(f"Cannot uniquely locate {name} in {file}: lines {hits}. Export its actual line.")
            line = hits[0]
        record.update(file=file, line=line)
        indexed[name] = record
    missing = sorted(set(expected) - set(indexed))
    if missing:
        fail("Blueprint declarations missing exported Lean metadata: " + ", ".join(missing))
    if md.get("checked_declarations") != len(records):
        fail("checked_declarations must equal the number of exported records.")
    return bp, md, indexed, sources


def graph_labels(title, lang):
    if lang != "zh-CN":
        return textwrap.wrap(title, width=29)
    # Count wide East Asian glyphs as two columns; mixed Latin/CJK titles fit
    # the same 230px nodes without truncating their mathematical wording.
    lines, current, width = [], "", 0
    for char in title:
        size = 0 if unicodedata.combining(char) else (2 if unicodedata.east_asian_width(char) in "WF" else 1)
        if current and width + size > 32:
            lines.append(current.strip())
            current, width = "", 0
        current += char
        width += size
    if current.strip():
        lines.append(current.strip())
    return lines


def graph(nodes, lang):
    ui = UI[lang]
    by_id = {n["id"]: n for n in nodes}
    levels, active = {}, set()

    def depth(key):
        if key in levels:
            return levels[key]
        if key in active:
            fail(f"Blueprint dependency cycle at {key}")
        active.add(key)
        value = max((depth(d) + 1 for d in by_id[key].get("dependencies", [])), default=0)
        active.remove(key)
        levels[key] = value
        return value

    layers = defaultdict(list)
    for node in nodes:
        layers[depth(node["id"])].append(node)
    width = max(760, max(map(len, layers.values())) * 250 + 40)
    height = len(layers) * 132 + 28
    positions = {}
    for level, layer in layers.items():
        for col, node in enumerate(layer):
            positions[node["id"]] = ((width - len(layer) * 250) / 2 + col * 250 + 10, level * 132 + 18)
    svg = [f'<svg class="dag" viewBox="0 0 {width} {height}" xmlns="http://www.w3.org/2000/svg" '
           'role="img" aria-labelledby="dag-title dag-description">',
           '<title id="dag-title">' + esc(ui["diagram_title"]) + '</title>',
           '<desc id="dag-description">' + esc(ui["diagram_description"]) + '</desc>',
           '<defs><marker id="arrow" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto"><path d="M0,0 L7,3.5 L0,7" style="fill:#a4b7bb;stroke:none"/></marker></defs>']
    for node in nodes:
        x, y = positions[node["id"]]
        for dep in node.get("dependencies", []):
            px, py = positions[dep]
            a, b, c, d = px + 115, py + 92, x + 115, y
            middle = (b + d) / 2
            svg.append(f'<path d="M{a},{b} C{a},{middle} {c},{middle} {c},{d - 3}" marker-end="url(#arrow)"/>')
    for number, node in enumerate(nodes, 1):
        x, y = positions[node["id"]]
        labels = graph_labels(node["title"], lang)
        if len(labels) > 4:
            fail(f"DAG title is too long to display fully: {node['title']}")
        svg.append(f'<a href="#{esc(node["id"])}" aria-label="{esc(node["title"])}"><title>{esc(node["title"])}</title>'
                   f'<rect x="{x}" y="{y}" width="230" height="92" rx="3"/>'
                   f'<text class="dag-number" x="{x + 12}" y="{y + 16}">{number:02d}</text>')
        for i, label in enumerate(labels):
            svg.append(f'<text x="{x + 115}" y="{y + 34 + i * 15}" text-anchor="middle">{esc(label)}</text>')
        svg.append('</a>')
    svg.append('</svg>')
    return ''.join(svg)


class LinkParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links = set(), []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if attrs.get("id"):
            if attrs["id"] in self.ids:
                fail(f"Duplicate HTML anchor: {attrs['id']}")
            self.ids.add(attrs["id"])
        for key in ("href", "src"):
            if attrs.get(key):
                self.links.append(attrs[key])


def check_links(directory):
    parsed = {}
    for file in sorted(directory.rglob("*.html")):
        parser = LinkParser()
        parser.feed(file.read_text(encoding="utf-8"))
        parsed[file.resolve()] = parser
    count = 0
    for file, parser in parsed.items():
        for link in parser.links:
            url = urlsplit(link)
            if url.scheme in {"http", "https", "mailto"}:
                continue
            if url.scheme or url.netloc or url.path.startswith("/"):
                fail(f"Nonrelative local link in {file.name}: {link}")
            target = (file.parent / unquote(url.path)).resolve() if url.path else file
            if not target.is_relative_to(directory.resolve()) or not target.is_file():
                fail(f"Broken local link in {file.relative_to(directory)}: {link}")
            if url.fragment and target in parsed and unquote(url.fragment) not in parsed[target].ids:
                fail(f"Broken anchor in {file.relative_to(directory)}: {link}")
            count += 1
    return count


def load_localization(english):
    global UI
    UI = read_json(TEMPLATE / "ui.json")
    if set(UI) != set(LOCALES) or set(UI["en"]) != set(UI["zh-CN"]):
        fail("UI localization must have complete, matching English and Chinese keys.")
    for key, value in UI["en"].items():
        translated = UI["zh-CN"][key]
        if isinstance(value, dict):
            if not isinstance(translated, dict) or set(value) != set(translated):
                fail(f"Incomplete UI dictionary: {key}")
            if any(not isinstance(x, str) or not x.strip() for x in translated.values()):
                fail(f"Empty UI translation: {key}")
        elif not isinstance(translated, str) or not translated.strip():
            fail(f"Missing UI translation: {key}")
    chinese = read_json(TEMPLATE / "zh-CN-blueprint.json")
    if chinese.get("language") != "zh-CN":
        fail("Chinese blueprint language must be zh-CN.")

    def structural(data):
        data = json.loads(json.dumps(data))
        for key in ("title", "scope", "dependency_semantics", "notation", "language"):
            data.pop(key, None)
        for node in data["nodes"]:
            for key in ("title", "explanation", "scope_caveats"):
                node.pop(key, None)
            node.get("contribution", {}).pop("detail", None)
        for ref in data.get("references", []):
            ref.pop("title", None)
            ref.pop("role", None)
        return data

    if structural(english) != structural(chinese):
        fail("Chinese blueprint changes mathematical/source structure: IDs, math, Lean links, dependencies and references must match exactly.")
    if set(chinese.get("notation", {})) != set(english.get("notation", {})):
        fail("Chinese blueprint must translate every notation entry.")
    fields = [("title", chinese.get("title")), ("scope", chinese.get("scope")),
              ("dependency_semantics", chinese.get("dependency_semantics"))]
    fields += [("notation." + k, v) for k, v in chinese.get("notation", {}).items()]
    for original, node in zip(english["nodes"], chinese["nodes"]):
        for key in ("title", "explanation"):
            fields.append((node["id"] + "." + key, node.get(key)))
        fields.append((node["id"] + ".contribution", node.get("contribution", {}).get("detail")))
        if len(node.get("scope_caveats", [])) != len(original.get("scope_caveats", [])):
            fail(f"Chinese scope caveats do not cover {node['id']}")
        fields += [(node["id"] + ".scope", value) for value in node.get("scope_caveats", [])]
    for key, value in fields:
        if not isinstance(value, str) or not re.search(r"[\u3400-\u9fff]", value):
            fail(f"Chinese prose coverage is missing: {key}")
    for ref in chinese.get("references", []):
        if not ref.get("title") or not ref.get("role"):
            fail(f"Missing translated reference fields: {ref.get('id')}")
    return chinese, len(fields)


def render_language(bp, records, sources, maths, args, lang):
    ui = UI[lang]
    nodes = bp["nodes"]
    by_id = {n["id"]: n for n in nodes}
    refs = {r["id"]: r for r in bp.get("references", [])}
    pages = {}
    incomplete = ('<aside class="notice">' + esc(ui["development"]) + '</aside>' if args.without_pdf else '')
    main = by_id.get("uniform_product_estimate", nodes[-1])
    body = f'<p class="kicker">{esc(ui["home_kicker"])}</p><h1>{esc(ui["home_title"])}<br>{esc(ui["home_subtitle"])}</h1>'
    body += f'<p class="authors">{esc(AUTHORS[lang])}</p>'
    body += paragraphs(bp["scope"]).replace('<p>', '<p class="lead">', 1) + incomplete
    body += '<div class="reading-grid">'
    if not args.without_pdf:
        pdf_link = '../note.pdf' if lang == 'zh-CN' else 'note.pdf'
        body += f'<a href="{pdf_link}"><strong>{esc(ui["read_pdf"])}</strong><span>{esc(ui["pdf_detail"])}</span></a>'
    body += f'<a href="blueprint.html"><strong>{esc(ui["read_blueprint"])}</strong><span>{esc(ui["blueprint_detail"])}</span></a></div>'
    body += f'<section class="theorem"><h2>{esc(ui["main_title"])}</h2>'
    body += paragraphs(main["explanation"]) + maths[main["id"]]
    body += f'<p><a href="blueprint.html#{esc(main["id"])}">{esc(ui["main_link"])}</a></p></section>'
    body += f'<section class="abstract"><h2>{esc(ui["scope_title"])}</h2>'
    body += paragraphs(ui["scope_first"]) + paragraphs(ui["scope_second"])
    body += f'<h2>{esc(ui["reading_title"])}</h2>' + paragraphs(ui["reading_intro"]) + '<ul>'
    for target, key in [('blueprint.html', 'reading_blueprint'), ('declarations.html', 'reading_declarations'), ('sources.html', 'reading_sources')]:
        body += f'<li><a href="{target}">{esc(ui[key])}</a></li>'
    body += f'</ul></section><h2>{esc(ui["references"])}</h2><ul class="reference-list">'
    for ref in refs.values():
        body += '<li>' + external_link(ref["url"], ref["title"]) + '<br>' + esc(ref.get("role", "")) + '</li>'
    body += '</ul>'
    pages['index.html'] = page(ui['overview'], body, 'index.html', 'index', lang, 'home')

    body = f'<p class="kicker">{esc(ui["exposition"])}</p><h1>{esc(ui["blueprint"])}</h1>' + paragraphs(bp.get('dependency_semantics', ''))
    body += f'<details class="graph-shell" open><summary>{esc(ui["diagram_summary"])}</summary><div class="graph-scroll">' + graph(nodes, lang) + '</div></details>'
    body += f'<nav class="contents" aria-label="{esc(ui["contents"])}"><ol>'
    body += ''.join(f'<li><a href="#{esc(n["id"])}">{esc(n["title"])}</a></li>' for n in nodes) + '</ol></nav>'
    body += f'<details><summary>{esc(ui["notation"])}</summary><dl>'
    for name, value in bp.get('notation', {}).items():
        if name not in ui['notation_labels']:
            fail(f'Missing notation UI label: {name}')
        body += f'<dt>{esc(ui["notation_labels"][name])}</dt><dd>{esc(value)}</dd>'
    body += '</dl></details>'
    for number, node in enumerate(nodes, 1):
        body += f'<article class="node" id="{esc(node["id"])}"><a class="back-top" href="#main">{esc(ui["back_contents"])}</a>'
        kind = node.get('kind', 'result')
        if kind not in ui:
            fail(f'Missing node kind translation: {kind}')
        body += f'<div class="node-kind">{number:02d} · {esc(ui[kind])}</div><h2>{esc(node["title"])}</h2>'
        body += maths[node['id']] + paragraphs(node.get('explanation', '')) + f'<dl><dt>{esc(ui["prerequisites"])}</dt><dd>'
        body += (', '.join(f'<a href="#{esc(d)}">{esc(by_id[d]["title"])}</a>' for d in node.get('dependencies', [])) or esc(ui['no_prerequisites'])) + '</dd>'
        contribution = node.get('contribution', {})
        category = contribution.get('category')
        if category not in ui['contribution_labels']:
            fail(f'Missing contribution category translation: {category}')
        body += f'<dt>{esc(ui["contribution"])} · {esc(ui["contribution_labels"][category])}</dt><dd>{esc(contribution.get("detail", ""))}</dd>'
        body += f'<dt>{esc(ui["limitations"])}</dt><dd>' + listing(node.get('scope_caveats', [])) + '</dd>'
        body += f'<dt>{esc(ui["declarations"])}</dt><dd><ul class="decl-links">'
        for group in node.get('lean', []):
            for name in group.get('declarations', []):
                rec = records[name]
                body += f'<li><a href="{declaration_url(name)}">{esc(name)}</a> · <a href="{source_url(rec["file"], rec["line"])}">{esc(ui["source_line"].format(line=rec["line"]))}</a></li>'
        body += f'</ul></dd><dt>{esc(ui["reference_label"])}</dt><dd>'
        node_refs = []
        for ref_id in node.get('source_references', []):
            if ref_id not in refs:
                fail(f'Unknown source reference: {ref_id}')
            ref = refs[ref_id]
            node_refs.append(external_link(ref['url'], ref['title']))
        body += '; '.join(node_refs) + '</dd></dl></article>'
    pages['blueprint.html'] = page(ui['blueprint_title'], body, 'blueprint.html', 'blueprint', lang)

    body = f'<p class="kicker">{esc(ui["exported"])}</p><h1>{esc(ui["catalogue_title"])}</h1>'
    body += paragraphs(ui['catalogue_intro']) + paragraphs(ui['original_language'])
    body += f'<div class="search-box"><label class="search-label" for="declaration-search">{esc(ui["search_label"])}</label>'
    body += f'<input type="search" id="declaration-search" data-search=".declaration" data-count="declaration-count" data-count-template="{esc(ui["search_count"])}" placeholder="{esc(ui["search_placeholder"])}" autocomplete="off">'
    body += f'<div id="declaration-count" class="search-count" aria-live="polite">{esc(ui["entries"].format(total=len(records)))}</div></div><noscript>{esc(ui["no_script"])}</noscript>'
    node_membership = defaultdict(list)
    for node in nodes:
        for group in node.get('lean', []):
            for name in group.get('declarations', []):
                node_membership[name].append(node)
    for name, rec in sorted(records.items()):
        body += f'<article class="declaration" id="{esc(anchor(name))}"><h2>{esc(name)}</h2>'
        body += f'<p class="meta"><a href="{source_url(rec["file"], rec["line"])}">{esc(rec["file"])} · {esc(ui["line"].format(line=rec["line"]))}</a></p>'
        if rec.get('docstring'):
            body += f'<p class="doc-label">{esc(ui["original_docstring"])}</p><div class="docstring">{esc(rec["docstring"])}</div>'
        body += '<pre class="signature" lang="en"><code>' + esc(rec['type']) + '</code></pre>'
        axioms = rec.get('axioms')
        if axioms is None:
            axiom_text = ui['axiom_missing']
        elif isinstance(axioms, list):
            axiom_text = ui['axioms'] + ': ' + (', '.join(map(str, axioms)) or ui['none'])
        else:
            axiom_text = ui['axioms_exported'] + ': ' + str(axioms)
        body += f'<p class="axioms">{esc(axiom_text)}</p>'
        if node_membership[name]:
            body += f'<p class="tagline">{esc(ui["blueprint"])}: ' + '; '.join(f'<a href="blueprint.html#{esc(n["id"])}">{esc(n["title"])}</a>' for n in node_membership[name]) + '</p>'
        body += '</article>'
    pages['declarations.html'] = page(ui['declarations'], body, 'declarations.html', 'declarations', lang)

    body = f'<p class="kicker">{esc(ui["lean_source"])}</p><h1>{esc(ui["source_title"])}</h1>' + paragraphs(ui['source_intro']) + '<ul class="file-list">'
    for file, text in sorted(sources.items()):
        body += f'<li><a href="{source_url(file)}">{esc(file)}</a> <span class="tagline">({esc(ui["lines"].format(total=len(text.splitlines())))})</span></li>'
        filename = 'source/' + file + '.html'
        prefix = '../' * (len(Path(filename).parts) - 1)
        source_body = f'<p class="kicker">{esc(ui["lean_source"])}</p><h1>{esc(file)}</h1><p><a href="{prefix}sources.html">{esc(ui["all_sources"])}</a></p>'
        linked = [(name, r) for name, r in records.items() if r['file'] == file]
        if linked:
            source_body += f'<details><summary>{esc(ui["catalogue_here"])}</summary><ul class="decl-links">'
            source_body += ''.join(f'<li><a href="{prefix}{declaration_url(n)}">{esc(n)}</a> · <a href="#L{r["line"]}">{esc(ui["line"].format(line=r["line"]))}</a></li>' for n, r in linked) + '</ul></details>'
        source_body += f'<div class="source-code" aria-label="{esc(ui["numbered_source"])}" lang="en">'
        for line, value in enumerate(text.splitlines(), 1):
            source_body += f'<div class="source-line" id="L{line}"><a class="line-no" href="#L{line}" aria-label="{esc(ui["line"].format(line=line))}">{line}</a><code>{esc(value) or " "}</code></div>'
        source_body += '</div>'
        pages[filename] = page(file, source_body, filename, 'sources', lang, 'source-page')
    pages['sources.html'] = page(ui['source_title'], body + '</ul>', 'sources.html', 'sources', lang)
    return pages


def check_language_coverage(pages, source_count):
    english = {k: v for k, v in pages.items() if not k.startswith('zh/')}
    chinese = {k[3:]: v for k, v in pages.items() if k.startswith('zh/')}
    if set(english) != set(chinese) or len(english) != source_count + 4:
        fail('Language page sets are incomplete or asymmetric.')
    for name, en in english.items():
        zh = chinese[name]
        ep, zp = LinkParser(), LinkParser()
        ep.feed(en); zp.feed(zh)
        if ep.ids != zp.ids:
            fail(f'Language anchor sets differ: {name}')
        for code, content in [('en', en), ('zh-CN', zh)]:
            if f'<html lang="{code}">' not in content:
                fail(f'Missing language identification: {code}/{name}')
            bylines = re.findall(r'<p class="authors">(.*?)</p>', content)
            expected_bylines = [esc(AUTHORS[code])] if name == 'index.html' else []
            if bylines != expected_bylines or content.count(AUTHORS[code]) != len(expected_bylines):
                fail(f'Incorrect homepage-only byline: {code}/{name}')
            if code == 'en' and ('龙维汉' in content or '(AI model)' in content):
                fail(f'Unexpected English author annotation: {name}')
            if content.count('data-language-switch=') != 1 or content.count('class="globe"') != 1:
                fail(f'Missing language navigation: {code}/{name}')
            if content.count(f'<span class="language-label">{esc(UI[code]["language_label"])}</span>') != 1:
                fail(f'Missing visible language label: {code}/{name}')
            if 'poincare-progress' in content or '100%' in content:
                fail(f'Private progress information leaked into {code}/{name}')
        # The exact exported type text must remain identical in both catalogues.
        if name == 'declarations.html':
            signatures = lambda text: re.findall(r'<pre class="signature"[^>]*><code>(.*?)</code></pre>', text, re.S)
            if signatures(en) != signatures(zh) or any('⋯' in x for x in signatures(en)):
                fail('Translated catalogue changed or truncated Lean signatures.')
        if name.startswith('source/'):
            source_lines = lambda text: re.findall(r'<code>(.*?)</code>', text, re.S)
            if source_lines(en) != source_lines(zh):
                fail(f'Translated source text differs: {name}')
    return len(english)


def build(args):
    bp, metadata, records, sources = load_inputs()
    zh, translated_fields = load_localization(bp)
    pdf = ROOT / 'paper/curve-estimates.pdf'
    if not args.without_pdf and not pdf.is_file():
        fail('paper/curve-estimates.pdf is missing. --without-pdf is for an explicitly incomplete development site only.')
    nodes = bp['nodes']
    result = subprocess.run([args.node, str(ROOT / 'scripts/render_math.cjs')],
                            input=json.dumps([n['math_statement'] for n in nodes]), text=True, capture_output=True, check=False)
    if result.returncode:
        fail('MathML rendering failed:\n' + result.stderr.strip())
    mathml = json.loads(result.stdout)
    if len(mathml) != len(nodes) or any('<math' not in m for m in mathml):
        fail('Math renderer returned invalid output.')
    maths = {n['id']: '<div class="math">' + rendered + '</div>' for n, rendered in zip(nodes, mathml)}
    pages = render_language(bp, records, sources, maths, args, 'en')
    pages.update({'zh/' + name: value for name, value in render_language(zh, records, sources, maths, args, 'zh-CN').items()})
    language_pages = check_language_coverage(pages, len(sources))

    # Only the renderer-owned staging directory is replaced before validation.
    OUT.mkdir(exist_ok=True)
    staging = OUT / ".build"
    if staging.exists():
        shutil.rmtree(staging)
    staging.mkdir()
    for filename, content in pages.items():
        path = staging / filename
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    (staging / "assets").mkdir()
    for filename in ("site.css", "site.js"):
        shutil.copyfile(TEMPLATE / filename, staging / "assets" / filename)
    if not args.without_pdf:
        shutil.copyfile(pdf, staging / "note.pdf")
    checked_links = check_links(staging)
    manifest = {"complete": not args.without_pdf, "blueprint_nodes": len(nodes),
                "declarations": len(records), "source_files": len(sources), "mathml_formulas": len(maths),
                "html_pages": len(pages), "checked_local_links": checked_links,
                "languages": list(LOCALES), "pages_per_language": language_pages,
                "checked_translated_fields": translated_fields, "language_structure_identical": True,
                "language_anchors_identical": True, "lean_signatures_identical": True,
                "authors": AUTHORS,
                "chinese_blueprint_sha256": hashlib.sha256((TEMPLATE / "zh-CN-blueprint.json").read_bytes()).hexdigest(),
                "ui_sha256": hashlib.sha256((TEMPLATE / "ui.json").read_bytes()).hexdigest(),
                "checked_declarations": metadata.get("checked_declarations"),
                "blueprint_sha256": hashlib.sha256((ROOT / "blueprint/blueprint.json").read_bytes()).hexdigest(),
                "metadata_sha256": hashlib.sha256((ROOT / "verification/blueprint-declarations.json").read_bytes()).hexdigest(),
                "math_renderer": "KaTeX 0.16.22; build-time MathML; strict errors",
                "pdf_included": not args.without_pdf}
    (staging / "build-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    # Publish only after inputs, math, source resolution and every local link passed.
    for child in list(OUT.iterdir()):
        if child != staging:
            if child.is_dir():
                shutil.rmtree(child)
            else:
                child.unlink()
    for child in list(staging.iterdir()):
        shutil.move(str(child), str(OUT / child.name))
    staging.rmdir()
    print(json.dumps(manifest, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--without-pdf", action="store_true", help="Build an explicitly incomplete development site.")
    parser.add_argument("--node", default="node", help="Path to an existing Node.js executable.")
    parser.add_argument("--check-links-only", action="store_true", help="Validate all existing generated HTML links and anchors.")
    args = parser.parse_args()
    try:
        if args.check_links_only:
            if not (OUT / "index.html").is_file():
                fail("No generated site exists.")
            print(f"Checked {check_links(OUT)} local links and anchors.")
        else:
            build(args)
    except (ValueError, OSError, subprocess.SubprocessError, KeyError, TypeError) as error:
        print(f"Site build failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
