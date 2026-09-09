# Independent bilingual publication-tooling review

Review date: 2026-09-09. Reviewer: independent GPT-6 Astra subagent. Scope: the frozen bilingual site builder, templates, localization inputs and verification-script change. Result: **accepted for the requested bilingual/offline publication behavior**, with one optional navigation improvement below. This review does not certify a new Lean build or a hosted CI run; the parent task performs the complete Lean verification separately. Chinese mathematical prose was reviewed independently by another reviewer.

## Actual checks

- Read the seven files recorded below. Inspected the current `verify.py` Git diff: its only change is removal of `VERSION` from the hash inputs. The recursive `website-template` file enumeration remains intact and covers both new JSON files. Lean sources, audits, configuration, scripts, paper PDF, workflow and third-party inputs remain in the recorded source set. Release-version identity therefore belongs to the release/package evidence rather than this mathematical verification snapshot.
- Loaded actual blueprint and Lean-export metadata through the builder; checked localization structure and generated pages without rebuilding or changing the site. There are 98 HTML pages: 49 English at the root and the identical set of 49 Chinese pages under `zh/` (45 source pages plus four navigation pages each). The builder’s link checker accepted 17,790 local links and anchors.
- Independently resolved all 196 language-switch links against their containing page, including deeply nested source pages: every target is the corresponding page in the selected language. All paired anchor sets match. Both catalogues contain the same 62 complete Lean signatures; no HTML page contains `⋯`.
- Localization validation checks preserved mathematical statements, node IDs, dependency edges, Lean file/declaration mappings and reference identifiers/URLs by structural equality. Three in-memory negative tests independently changed a formula, dependency list or Lean mapping; all were rejected with `ValueError`. No real input was modified. The checked Chinese-prose coverage contains 103 fields.
- Executed the actual JavaScript in a Node VM with minimal DOM mocks for both HTTPS and `file://` URLs. Confirmed query initialization, text filtering/counts, input updates when `history.replaceState` throws, language-switch propagation of the live query and fragment, context-menu propagation, and valid hash-change clearing/scrolling. This is a behavioral unit exercise, not a claim of a full browser visual audit. With JavaScript disabled, the generated page already contains all declarations and ordinary language links; filtering is optional enhancement.
- Inspected all HTML runtime-resource attributes: scripts, styles and other embedded resources have relative local URLs. The CSS uses system fonts, with no remote font/import dependency; JavaScript has no fetch, package loader or network runtime. Mathematical rendering is precomputed MathML. External bibliography links remain ordinary intentional hyperlinks requiring a connection.
- Every generated page identifies `GPT-6 Astra · Juii-hang Leung（龙维汉）`, with the AI disclosure present in the shared template. No page contains `v0.1.0-review`, `100%`, `poincare-progress`, or an href/src pointing to a progress path.

## Optional navigation improvement

A manually constructed initial declaration URL combining a query that excludes the fragment target with that target’s hash can leave the target filtered out. The script clears filtering on subsequent `hashchange`, but does not apply that treatment on initial page load. Ordinary matching query/anchor navigation and the tested hash-change path work. This is a nonblocking usability edge case; a future change could apply the same initial-fragment visibility rule. No implementation was changed for this review.

## Reviewed source SHA-256

| File | SHA-256 |
| --- | --- |
| `scripts/build_site.py` | `104c90ac1f91f888410b45e54d77870f78a975fcfbd35e6b57e962e3c712c800` |
| `scripts/verify.py` | `443bbe75c9dbe5ed9912d273bedaf53be68b298153ac2dc2c9136451f80598ac` |
| `website-template/page.html` | `3e2efd821c2f3b4dddf01f3c5e1e41452df86c12f2b7eae884c4b389529558a1` |
| `website-template/site.css` | `7e9cc62191144ecec68d72a7ea7cebbb68a39ddb32ed1a32db2b0bd86134de12` |
| `website-template/site.js` | `3d0c577b447476027f4d3055baef433186b995ea212beff3c295e03f16c736ec` |
| `website-template/ui.json` | `a5a08903441026436364e5428677c22c42481e2a096097b94907e08519ba9bb3` |
| `website-template/zh-CN-blueprint.json` | `d0ff17b00497866bde3c63af1665e1ae42a60bb36762eae2be41ca756e7f7822` |

The site’s checked metadata SHA-256 is `6bde2b1e36866c42f9f8c9fad011aedb589e0a1bcb9f708bcbe001bf4c54dcf5`; its blueprint SHA-256 is `a50e6ca7f6cef9a042b062fef4e11ad8d646fde766e9053bd6aec2d30bce6e84`. Generated-site/package hashes should be bound by the final release evidence. No Lake command, dependency download, mathematical source edit, or implementation edit was performed in this review.
