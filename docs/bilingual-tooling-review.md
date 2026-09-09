# Independent bilingual UI tooling review

2026-09-09 — Independent GPT-6 Astra subagent review of the frozen minimal-presentation UI changes. **Source review, simulated behavior and final generated-page checks: PASS.** The final generated site was checked after the parent completed generation; no formal site rebuild was run by this reviewer.

Read all five files below and their diff relative to HEAD. The change places an author byline only in the language-specific homepage body: English `GPT-6 Astra · Juii-hang Leung`; Chinese `GPT-6 Astra · Juii-hang Leung（龙维汉）`. Shared pages contain no byline, footer, AI annotation or footer disclaimer. One inline SVG globe with a short visible `Language` / `语言` label replaces the two language choices; its accessible label/title states the destination language, and its ordinary relative link targets the corresponding page in the other language.

Actual lightweight checks (no formal site build):

- Rendered ten in-memory template variants: both languages across homepage, blueprint, declaration catalogue, source index and a deeply nested source page. Checked exactly one homepage byline, zero elsewhere, no footer/AI annotation, one globe, correct accessible label/title and exact opposite-language relative target.
- Executed the real JavaScript in Node VM DOM simulations for HTTPS and file URLs. An initial search query excluding the fragment target leaves that target visible, preserving both query and hash. Filtering/counts, later hash changes, scrolling, malformed percent-encoded fragments, an exception from `history.replaceState`, empty-query removal, and click/contextmenu/focus language-switch context propagation all passed. This resolves the earlier review’s initial query/hash usability observation.
- Inspected the source diff: exported Lean signatures and source rendering remain unchanged. The coverage checker still compares signatures and now additionally compares both language versions’ source code blocks. Formula rendering is outside these UI edits. Mathematical prose review is assigned separately.
- The globe is inline SVG, CSS uses system fonts, and the JavaScript adds no network loading. Ordinary links and complete page content remain usable without JavaScript. These checks are not a full browser visual audit, a Lean verification or a hosted CI result.

No blocking issue found. Only this review document was written; implementation, mathematical files, PDF, generated website, dashboard and acceptance evidence were not modified.

## Frozen UI source hashes

| File | SHA-256 |
| --- | --- |
| `scripts/build_site.py` | `d126f053b0f610d86f7440444e73761bf851ba6c5904db248c1411bfb70e992b` |
| `website-template/page.html` | `c8e1c11199cb867089247cf60db16d9ee2e20dc27bed8acc318a06020a077a3d` |
| `website-template/site.css` | `2c28c46bb871e1ef820e80d16d2ed9ee49efce68aad4d7e1178ae19a5a04af64` |
| `website-template/site.js` | `8a9a8efb519e842fcc39afe1e0e2bb9e553753a548a2eb664b095dd014030d89` |
| `website-template/ui.json` | `a6f6988ec920b7c1bd1c67395d30a2c350dd36902122a6f6f2634ecdef5fbe35` |

## Final generated-site check

Ran `python3 scripts/build_site.py --check-links-only` successfully: **17,692 local links and anchors**. Independently parsed all **98 HTML pages** (49 English and 49 Chinese): exactly two bylines in total, each solely on its language’s homepage with the specified name; all other pages have none. Every page has exactly one inline globe, whose destination, `hreflang`, `aria-label` and `title` are correct, including nested source pages. No page contains the old footer, AI annotation, review-version string, private dashboard percentage/reference, progress link or `⋯`.

The paired page sets and anchors match. The 62 Lean signatures and all 45 source pages’ code blocks are identical across languages. Reloading both actual blueprint inputs passes the builder’s mathematical/source structure equality check. All embedded HTML runtime resource URLs remain relative and local. The final five UI source hashes are recorded above; the visible-label increment changes the builder, CSS and UI JSON only. The page template and JavaScript hashes remain unchanged. The parent performs the separate browser interaction/visual check and full release acceptance.

Final input/build-manifest hashes:

- English blueprint: `e5f208da45b9c2cccadccda88f6a71b85d339228d1615329c772cb23027cebe8`.
- Chinese blueprint: `f31199b3553c7a308257d041134a4d4c46f0cd9c9553c866c08ee7ff770855bc`.
- `website/build-manifest.json`: `51251ae74427c80d54ef0c69f27dfc91f68ac8405b49556c680ecccf3b37c96a`.

No blocking issue found in this independent UI/tooling scope.

## Final visible-language-label increment

Read the small builder/CSS/localization increment and independently parsed all 98 regenerated pages. Every English page has exactly one visible `Language` label; every Chinese page has exactly one `语言` label. The accessible name and tooltip are exactly `Language: switch to Chinese` and `语言：切换至英文`, respectively, containing the visible label and correctly identifying the destination. All 98 links still resolve to the corresponding opposite-language page; `hreflang` agrees. CSS uses automatic width, inline flex and nonwrapping text. Homepage-only author placement and footer absence were rechecked.

JavaScript is byte-identical to the previously simulated version, so its query/hash preservation and initial-target visibility results remain applicable. Mathematical inputs and rendering are unchanged by this increment; the earlier structural checks remain applicable. The regenerated manifest continues to record 98 pages and 17,692 checked links. No new build or complex simulation was performed for this incremental review. **PASS; no blocking issue found.**
