# Portable reproduction

Run commands from the root of the published CurveControl project. Python 3.9 or newer and an existing Lean 4.32.1 toolchain are sufficient for source preparation. The preparation script does not install Lean or fetch proof binaries.

| Input | Fixed revision |
|---|---|
| Lean | `leanprover/lean4:v4.32.1` |
| mathlib4 | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| frenzymath/Poincare-Conjecture | `bb91a091f0b968f8bbe8d861e025a88d82b161be` |

## Reuse existing sources first

```sh
python3 scripts/prepare_dependencies.py \
  --mathlib /path/to/mathlib4 \
  --geometry /path/to/Poincare-Conjecture
python3 scripts/verify.py
```

The default mode is `reuse`. It checks the saved fingerprints for mathlib, the Ricci-flow library, DoCarmoLib and Shared before invoking `configure.py` and `lake update`. A missing or different source tree causes a failure, never an implicit source download or replacement. `lake update` may still obtain missing **transitive Lake packages**; this step is distinct from fetching the two primary source archives. The geometric repository must retain the Ricci-flow, Riemannian geometry, and shared source directories in their original relative positions.

Pass `--lake /path/to/lean-4.32.1/bin/lake` to both scripts if the toolchain is not on PATH. The preparation script checks that executable before configuring Lake. The verifier additionally checks the actual `lake env lean --version` result, repeats the dependency fingerprint check using the resolved Lake manifest, builds the library, and audits project declarations and their reachable axioms.

For a read-only source check, add `--check-only`. For preparation before Lean is available, add `--configure-only`: source validation and configuration run, but `lake update` and the executable check are deferred. All subprocess calls pass arguments as lists, so paths containing spaces are supported.

## Explicitly obtain missing sources

```sh
python3 scripts/prepare_dependencies.py --mode fetch --deps-dir /path/to/dependency-store
python3 scripts/verify.py
```

Only `--mode fetch` allows the script to obtain a missing primary dependency. It uses the GitHub codeload archive URL containing the full commit ID, validates the extracted Lean sources against the release fingerprint baseline, and then moves the prepared tree into its destination. Existing destinations are validated and reused; they are never overwritten. The default store, if omitted, is `.dependencies/` inside the project.

Mathlib is extracted as a complete source tree. The geometry archive is restricted to its three needed packages plus repository-level LICENSE/COPYING/NOTICE/README files. Package contents and layout are preserved, including nested attribution files; no Lean source is patched. Archive traversal, external symlinks, and unsupported special entries are rejected. The script downloads no binary caches, and uses temporary staging so a failed download or mismatch does not leave a seemingly valid destination.

An existing archive can be reused without a network request:

```sh
python3 scripts/prepare_dependencies.py --mode fetch \
  --mathlib /existing/mathlib4 \
  --geometry /new/Poincare-Conjecture \
  --geometry-archive /existing/Poincare-Conjecture-bb91a091.tar.gz
```

There is an analogous `--mathlib-archive` option. These options are consulted only when the corresponding destination is missing.

## Cache and isolated project builds

Matching mathlib caches can be reused. Without them Lean rebuilds dependencies from source, which can be substantially slower and require more disk space. The CI workflow requests the cache for the direct Mathlib imports in the project and selected geometry packages; the cache tool includes their transitive Mathlib dependencies. It does not use `cache get CurveControl.lean`, because the pinned mathlib cache parser does not traverse arbitrary geometry/project module namespaces.

To rebuild the project in isolation while sharing pinned dependency sources, copy the released project to a fresh directory, omit its `.lake` directory and `.dependencies`, and run `prepare_dependencies.py` with explicit paths to the already verified dependencies. Then run `verify.py` in that copy. Its project modules are rebuilt in the copy's independent `.lake/build`; the dependencies can retain their matching build caches. Concurrently mutating those shared sources or running overlapping builds in their same output directories is outside this reproduction procedure.

Local dependency paths in the new `lakefile.lean` and manifest will differ from the original release machine. A new passing release record should therefore contain new configuration hashes; byte-for-byte agreement with the original machine's path strings is not expected. The mathematical-source and dependency-tree fingerprints remain comparable.

## Source provenance checked for this release

The reviewed mathlib checkout has the exact fixed HEAD above and no tracked modifications. The original geometry archive has top directory `Poincare-Conjecture-bb91a091f0b968f8bbe8d861e025a88d82b161be`. Its 573 Ricci-flow, 293 Riemannian geometry, and 12 shared nonhidden Lean files were compared directly with the working snapshot: no differences were found, and all three archive-derived fingerprints match the released baseline.

The earlier task-local geometry extraction omitted the repository's root `LICENSE`; the original archive contains it at its root, not under a different package. Its actual text is Apache License 2.0 and SHA256 is `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`. Fresh extraction by this script preserves that file. Reusing the earlier extraction does not silently rewrite it; the exact Lean-source fingerprint remains the source identity check. Attribution and license information in the project distribution should be read together with the original dependency notices.

## Continuous integration

`.github/workflows/verify.yml` is intended for publishing this project as the repository root. It uses read-only repository permissions and these reviewed action revisions:

- [actions/checkout](https://github.com/actions/checkout/tree/11d5960a326750d5838078e36cf38b85af677262), fixed commit for v4.
- [official leanprover/lean-action v1.5.0](https://github.com/leanprover/lean-action/blob/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/action.yml), configured only to install/setup Lean; the project's verifier performs the build and audit.
- [actions/upload-artifact](https://github.com/actions/upload-artifact/tree/ea165f8d65b6e75b540449e92b4886f43607fa02), fixed commit for v4, preserving verification logs.

The official action's inputs and setup behavior were checked against its pinned metadata and scripts. Pinning that action does not imply its internal elan installer URL is immutable; the selected Lean release is separately checked by the preparation/verification scripts. This workflow has been source-reviewed, but has **not been run on hosted GitHub Actions** for this release. Local checks are not claimed as cloud CI success. Uploaded logs from a failed job are diagnostic artifacts, not a passing verification certificate.

The workflow also builds the offline HTML reference after Lean verification. It does not publish or deploy the site. A future public deployment requires an explicitly selected destination.

## Rebuild the mathematical reference

After `verify.py` exports the actual Lean types, run:

```sh
python3 scripts/build_site.py
python3 scripts/build_site.py --check-links-only
```

This requires Node.js on PATH (or `--node /path/to/node`). The small, pinned KaTeX build tool is bundled under `third_party/katex`; no npm installation is needed. The generated English `website/index.html` and Chinese `website/zh/index.html` work offline. Both language views share the same formula strings, declaration mappings and source text. The build validates the translated blueprint against the canonical English structure. Formulas are native MathML, with no runtime CDN or font download. Graph edges describe mathematical exposition prerequisites, not the complete Lean constant-dependency graph.

The eight-page report includes its LaTeX and BibTeX sources in `paper/`. With an existing Tectonic installation, compile from that directory using `tectonic curve-estimates.tex`. The Chinese author name uses xeCJK and the open FandolSong-Regular.otf font from the TeX bundle, without a machine-specific font path. The first run may fetch missing TeX resources; `tectonic --only-cached curve-estimates.tex` uses only a previously populated cache. The included PDF was built using Tectonic 0.17.0 and visually checked on all pages. Its source/PDF hashes are in `verification/note-check.json`. Rebuild the website after changing the PDF so its included copy stays current.
