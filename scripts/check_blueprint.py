#!/usr/bin/env python3
"""Validate curated graph and report mappings against Lean-exported declarations."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[1]

def main():
    data = json.loads((ROOT / 'blueprint/blueprint.json').read_text())
    exported = json.loads((ROOT / 'verification/blueprint-declarations.json').read_text())
    nodes = {n['id']: n for n in data['nodes']}
    if not len(nodes) == len(data['nodes']):
        raise ValueError('Duplicate node ids')
    refs = {r['id'] for r in data['references']}
    if not len(refs) == len(data['references']):
        raise ValueError('Duplicate references')
    records = {r['declaration']: r for r in exported['records']}
    if not len(records) == len(exported['records']) == exported['checked_declarations']:
        raise ValueError('Blueprint validation failed')
    if not not exported['extra_axioms']:
        raise ValueError('Blueprint validation failed')
    mapped = set()
    active, done = (set(), set())

    def visit(key):
        if not key in nodes:
            raise ValueError(f'Missing prerequisite {key}')
        if not key not in active:
            raise ValueError(f'Cycle at {key}')
        if key in done:
            return
        active.add(key)
        for dependency in nodes[key]['dependencies']:
            visit(dependency)
        active.remove(key)
        done.add(key)
    for key, node in nodes.items():
        visit(key)
        if not set(node['source_references']) <= refs:
            raise ValueError('Blueprint validation failed')
        for entry in node['lean']:
            source = ROOT / entry['file']
            if not (source.is_file() and source.resolve().is_relative_to(ROOT)):
                raise ValueError('Blueprint validation failed')
            if not entry['file'] == entry['module'].replace('.', '/') + '.lean':
                raise ValueError('Blueprint validation failed')
            for declaration in entry['declarations']:
                mapped.add(declaration)
                if not declaration in records:
                    raise ValueError(f'Unresolved {declaration}')
                record = records[declaration]
                if not record['module'] == entry['module']:
                    raise ValueError(f'Module mismatch: {declaration}')
                if not record['type'].strip():
                    raise ValueError('Blueprint validation failed')
                if '⋯' in record['type']:
                    raise ValueError('Truncated Lean type: ' + declaration)
                if not set(record['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}:
                    raise ValueError('Blueprint validation failed')
    if not mapped == set(records):
        raise ValueError('Blueprint export is stale')
    paper = ROOT / 'paper/curve-estimates.tex'
    paper_mappings = re.findall('\\\\leanref\\{([^{}]+)\\}\\{([^{}]+)\\}', paper.read_text())
    paper_mappings = [(name, module) for name, module in paper_mappings if not name.startswith('#')]
    if not paper_mappings:
        raise ValueError('No report declaration references found')
    for declaration, module in paper_mappings:
        if not declaration in records:
            raise ValueError(f'Report declaration missing: {declaration}')
        expected = records[declaration]['module'].replace('.', '/') + '.lean'
        if not module == expected:
            raise ValueError(f'Report file mismatch: {declaration}')
    inputs = ['blueprint/blueprint.json', 'verification/blueprint-declarations.json', 'paper/curve-estimates.tex', 'BlueprintAudit.lean']
    report = {'status': 'passed', 'node_count': len(nodes), 'declaration_count': len(records), 'paper_reference_count': len(paper_mappings), 'acyclic': True, 'scope': 'Declaration/type correspondence and curated graph integrity; not semantic peer review.', 'sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in inputs}}
    (ROOT / 'verification/blueprint-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))
if __name__ == '__main__':
    main()
