# Isolated project reproduction

The complete project was rebuilt successfully in `work/postprocess/reproduction/project` on the same machine. This is an isolated project rebuild, **not a fresh-machine or dependency-cold reproduction**.

The initial project `.lake/build` directory did not exist. No project `.olean` or build directory was copied. The run reused the existing Lean 4.32.1 toolchain, the fingerprint-checked mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`, and geometry commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`, including their external dependency build caches. Eight transitive packages were linked to their existing external package directories.

`prepare_dependencies.py --mode reuse --mathlib … --geometry … --lake …` completed, including `lake update`, with exit 0. Then `verify.py --lake …` ran without `--skip-build` and exited 0. The build completed 3211 Lake jobs and newly compiled all 44 mathematical source modules plus the root. The environment audit checked 796 declarations across 45 modules, with no extra axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. Blueprint export and checks also passed.

All 45 mathematical source hashes match the original project and the copied audit scripts remained unchanged in the original through verification. Exact absolute commands, source hashes, dependency links, timestamps, exit codes, and log hashes are recorded in [reproduction-check.json](../verification/isolated-reproduction/reproduction-check.json). Independent [release-check.json](../verification/isolated-reproduction/release-check.json), [reachable-axioms.json](../verification/isolated-reproduction/reachable-axioms.json), and the build/audit logs are stored alongside it. The main release evidence was not overwritten.

After success, only the temporary project's own `.lake/build` was removed to recover disk space; source copies and verification evidence remain. External dependencies and the original project were not cleaned or changed by this reproduction. This mechanical check does not replace the separate mathematical and semantic reviews.

After this run, an independent blueprint review tightened one explanatory caveat: the exposed energy roots assume a lower Ricci bound for all ambient unit vectors. At that stage, exactly three inputs differed from the isolated record: the two intentionally reconfigured Lake files and that blueprint prose. The primary release was reverified after the correction.

The later authored, bilingual presentation changes the report front matter, site and verification tooling while retaining every mathematical source and declaration mapping. See [presentation-math-preservation.json](../verification/presentation-math-preservation.json) for the exact comparison. The current [release-check.json](../verification/release-check.json) covers the current inputs. The isolated evidence retains its original source hashes and is not relabeled as a new-machine or new-presentation rebuild.
