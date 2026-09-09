# Publication tooling review

**Final review status: PASS after remediation.** The historical findings below were corrected and regression-tested; the final export contains 62 complete mapped types with no ellipses. The final section records the accepted hashes and evidence. Hosted GitHub CI has not been run.

Date: 2026-09-09. Read-only review; no Lake build or Lean/source modification performed. Lightweight tests used temporary copies or read-only link checking. Reviewer previously authored prepare_dependencies.py and the initial CI workflow; the blueprint export/checker and site renderer were independently reviewed here. This is not evidence that hosted GitHub CI has run.

## Reviewed file identities

| File | SHA256 at review |
|---|---|
| scripts/prepare_dependencies.py | `09b6211317284d44e00cfd02482521bf7fea5345b25e5e79633d2359757bce62` |
| scripts/verify.py | `ee97e5f34bc960f551a49272f042d0cb820ded2df1eb0562b0af4467d04b72b2` |
| scripts/check_blueprint.py | `4ba01df28ddd81b1a7181e947dd09051feb0fc219a8047849c4e74a9248e7f7c` |
| scripts/build_site.py | `648bf8e7b50270395e1a9ccfe24ee709d1a79682422a100ba32b470135382095` |
| BlueprintAudit.lean | `2b745b673c9969104c0ee924fe1c3e3c8dd8b65989ca7542262bd6df97d23e84` |
| .github/workflows/verify.yml | `19eb1ef7ea1e87d2a9c82d13a85228c615b80116af5824da67f0d88f36deedc6` |

## Findings needing correction

### 1. Exported final theorem types are truncated

The current 61-record `verification/blueprint-declarations.json` includes five types containing `⋯`. Some are proof-term omissions, but the main uniform product theorem, positive-scale theorem, and two example theorem types have their final conclusions replaced by `⋯`. For example the static product root ends with `∀ (ℓ : Λ) (i : ι) (t : ℝ), ⋯`.

`BlueprintAudit.lean` uses default `Meta.ppExpr` limits. The declarations are genuinely resolved, but their displayed statements are not complete, contrary to the site's “complete printed statement” description. Increase/disable pretty-printer depth and step truncation during export, regenerate metadata, and check the root statements' actual conclusions are present. This does not affect kernel proof correctness; it affects the promised publication interface.

### 2. Blueprint integrity checks disappear in optimized Python

Every substantive guard in check_blueprint.py is an `assert`. I reproduced the failure on an isolated temporary project: replace one exported record's type with an empty string; ordinary Python exits 1 with AssertionError, whereas `python -O` exits 0 and writes a report with `status: passed`. `PYTHONOPTIMIZE=1` can cause the same behavior when inherited by verify.py.

Use explicit conditional exceptions (or reject optimized execution before any validation). The intended normal-mode coverage is good, but a verification tool should not issue a passing record when its checking logic has been disabled.

### 3. Publication asset hashes have narrower coverage than the generated site

The enhanced verifier hashes mathematical sources, both Lean audits, Python scripts, blueprint JSON, paper TeX/Bib, version, dependency baseline, and Lake configuration. This is strong proof/export input coverage. It does not hash render_math.cjs, website-template files, the vendored KaTeX files, the workflow, or the included PDF. The site's build manifest hashes only blueprint and exported metadata, not all rendered source/PDF/assets.

If release-check is intended only as the Lean/blueprint verification certificate, describe that scope and provide a separate publication manifest. If it is intended to bind the complete publication toolchain/bundle, include those source assets and record generated PDF/site checksums. A PDF merely existing is not a check that it was compiled from the current TeX. This is an artifact provenance improvement, separate from mathematical acceptance.

## Passing checks and design observations

- Actual declaration resolution is sound: BlueprintAudit reads names from the curated JSON, calls getConstInfo in the imported Lean environment, obtains defining module/docstring/range from Lean, and runs collectAxioms. It does not infer a theorem type from a source regex. The separate complete-project Audit remains in verify's ordered steps.
- In normal Python mode the checker rejects missing/duplicate node IDs and references, graph cycles, missing prerequisites, invalid source paths, module/file mismatches, unresolved names, stale export name sets, empty types, extra axioms, and incorrect report `\leanref` paths. It intentionally validates a curated exposition DAG, not a graph claimed to be extracted from proof terms; its report accurately excludes semantic peer review.
- The current exporter produces actual line numbers for all 61 mapped records. The site uses them, validates their range, escapes source/type text, creates line anchors, and checks every generated relative link. Its fallback source search fails on ambiguity instead of inventing a position. Running `build_site.py --check-links-only` on the current output passed **8791 local links/anchors**.
- Formula rendering uses the local KaTeX 0.16.22 bundle with strict syntax errors, trust=false, and build-time MathML. The generated pages do not depend on a remote formula-rendering service. The PDF-free flag marks the site incomplete. The renderer publishes its staging tree only after input/math/link checks succeed.
- Standalone site generation trusts the existing exported metadata; it does not itself refresh Lean or enforce export freshness against current source bytes. The CI order runs verify immediately before site generation, which supplies that intended provenance. A standalone user should follow that same order.
- prepare_dependencies defaults to reuse, never overwrites an existing source destination, and permits fetching only with explicit fetch mode. Fixed archive commit IDs and exact source fingerprints are enforced; extraction preserves the geometry root LICENSE and uses subprocess argument lists. The prior tested geometry archive source fingerprints match the working snapshot without source patching. Existing matching dependency source and build caches can be reused.
- verify resolves actual local dependencies from the manifest, checks the sibling package layout, validates the actual Lean executable version, requires matching dependency fingerprints, and compares its captured project input hashes before/after the build/audit. It labels skip-build mode explicitly. These protections remain intact after the blueprint additions.
- CI selects fixed action commits, configures the source paths before installing Lean, resolves dependencies, requests mathlib cache roots by their directly imported Mathlib names, then runs verifier and site builder. The pinned mathlib cache does not follow custom project namespaces, so explicitly enumerating Mathlib imports is the correct approach. The local enumeration found 247 roots and no entire Mathlib-root request. The workflow relies on the hosted Ubuntu runner's existing Node executable for the vendored renderer and on the tracked PDF being distributed. No TeX compiler or npm install is needed by the site step as written.
- The official lean-action source was previously checked at its pinned commit. Its internal elan installer uses an upstream moving URL; this limitation is already documented, while the Lean release selected for actual verification remains checked as 4.32.1. No hosted CI success is claimed.

## In-flight release state

At this review instant release-check.json was the earlier 2026-09-09T09:53:32 record. Its CurveControl.lean and scripts/verify.py hashes differed from the now-expanded publication project, as expected while the parent runs the new complete verification. This old record should not be presented as covering the new root/examples/blueprint workflow. A successful new record after the fixes must contain the blueprint export/check exit fields and match the final frozen inputs.

Overall: the publication chain is structurally well designed, but the truncated type export and optimized-Python assertion bypass should be fixed before claiming the blueprint reference is fully checked and complete. No new mathematical-source problem was identified.


## Remediation source review and regression checks

The parent changed the publication tools after the initial findings. Updated identities:

| File | SHA256 |
|---|---|
| scripts/prepare_dependencies.py | `09b6211317284d44e00cfd02482521bf7fea5345b25e5e79633d2359757bce62` |
| scripts/verify.py | `29dba8863e52290f71f430b8337e0286bb990b218910f1839be9d66f394844a6` |
| scripts/check_blueprint.py | `196b1f521dfa8110d2637cdb7dbe63dd87a3442f1fbcef8c29c9de5d41d63892` |
| scripts/build_site.py | `648bf8e7b50270395e1a9ccfe24ee709d1a79682422a100ba32b470135382095` |
| BlueprintAudit.lean | `59bf94255af994913118b36d82289c2023cd6b11687ff3088f252b85f58074c2` |
| .github/workflows/verify.yml | `19eb1ef7ea1e87d2a9c82d13a85228c615b80116af5824da67f0d88f36deedc6` |

The optimized-Python issue is resolved by explicit conditional ValueError guards. I repeated the isolated malformed-record tests: both an empty type and a type containing `⋯` now exit 1 under ordinary Python and `python -O` (four rejecting runs). No passing report is emitted by those test runs.

BlueprintAudit now enables deep terms/proof printing, increases the pretty-printer step budget, and throws if the actual printed type contains `⋯`. This prevents silently publishing a truncated type even if the printer options alone were insufficient. The checker independently rejects `⋯` as well. At the time of this source-remediation check the old export still contained five truncated records; acceptance of the final generated metadata remains pending the parent's new export run.

The verifier now also hashes the PDF, workflow, CJS renderer, every website-template file, and every third_party file. Together with the parent's planned whole-bundle manifest, this closes the stated publication-input hash gap. Site-generated files remain publication outputs rather than mathematical proof inputs.


## Final frozen review

The new Lean export is available and independently inspected:

- `verification/blueprint-declarations.json` SHA256: `6bde2b1e36866c42f9f8c9fad011aedb589e0a1bcb9f708bcbe001bf4c54dcf5`.
- 62 nonempty printed types; **zero** contain `⋯`.
- Both final uniform-product theorem types now explicitly include the length and total-curvature exponential conclusions (2395 and 2474 characters), rather than omitting those conclusions.
- A fresh isolated copy of the actual blueprint, metadata, paper references, and referenced Lean files passes the updated checker even under `python -O`: **22 nodes, 62 declarations, 21 report references**. Earlier malformed empty/truncated-type tests correctly failed in both optimized and ordinary modes.
- The parent's first expanded full build, complete-project axiom audit, blueprint export and blueprint checker all succeeded; its source-freeze check correctly refused that run's certificate because scripts changed during verification. A final frozen complete run is in progress. This review does not replace that run or claim its completion in advance.

Final reviewed tool identities:

| File | SHA256 |
|---|---|
| scripts/prepare_dependencies.py | `09b6211317284d44e00cfd02482521bf7fea5345b25e5e79633d2359757bce62` |
| scripts/verify.py | `29dba8863e52290f71f430b8337e0286bb990b218910f1839be9d66f394844a6` |
| scripts/check_blueprint.py | `196b1f521dfa8110d2637cdb7dbe63dd87a3442f1fbcef8c29c9de5d41d63892` |
| scripts/build_site.py | `648bf8e7b50270395e1a9ccfe24ee709d1a79682422a100ba32b470135382095` |
| BlueprintAudit.lean | `59bf94255af994913118b36d82289c2023cd6b11687ff3088f252b85f58074c2` |
| .github/workflows/verify.yml | `19eb1ef7ea1e87d2a9c82d13a85228c615b80116af5824da67f0d88f36deedc6` |

All three original findings are closed at the source/interface level: complete Lean statement printing is enforced and demonstrated, validation no longer depends on Python assertions, and verifier hashes include the publication renderer/assets/PDF/workflow. The parent will additionally bind final generated files in the package manifest. No further publication-tooling repair is required by this review. The remaining acceptance action is to use the successful frozen verification/package records, not the deliberately rejected earlier run. Site output should be regenerated from this exact 62-declaration export, as the parent is doing.
