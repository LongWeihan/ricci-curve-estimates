# Independent release reproducibility review

Date: 2026-09-09. Scope: read-only review of configure.py, verify.py, fingerprint_dependencies.py, Audit.lean, Lake configuration, README, current release JSON, and source hashes. No rebuild, download, or mathematical-source change was performed.

## Verified evidence

- Current `release-check.json` records a full build and audit, both exit 0. Independently hashing every recorded source found **no mismatches**.
- The tree contains 43 mathematical `.lean` modules plus the root. All 44 module names occur in the audit, and every mathematical source is included in the release source hash map.
- `reachable-axioms.json` contains exactly **757 distinct records**, no duplicate declaration names and no axiom outside `propext`, `Classical.choice`, `Quot.sound`.
- The source has three explicitly private theorems; all three appear under their mangled `_private...` names in the recorded audit. Generated declarations and instances are selected by defining module, not by a theorem-name regex or namespace heuristic.
- I independently ran the read-only dependency fingerprint `--check` against the current pinned mathlib/geometry directories. It returned **Dependency source fingerprints match** for mathlib (8795 Lean files), the Ricci-flow library (573), DoCarmoLib (293), and Shared (12).

## Audit mechanism

`Audit.lean` imports the root, enumerates every loaded environment constant whose defining module has the `CurveControl` Name prefix, then calls Lean's `collectAxioms` for each. I inspected Lean 4.32.1's implementation in `Lean/Util/CollectAxioms.lean`: it recursively collects constants appearing in checked declaration types and values, including theorem/definition/opaque bodies and constructors, and uses serialized transitive axiom results for imported modules. Consequently dependency axioms reachable through imported geometry or analysis are checked, not just axioms directly mentioned in project source.

The verifier separately compares all discovered project source-module names with the root's audited modules. This closes the usual gap where an unimported project file could be built but omitted from a root audit. It also rejects an empty declaration set. The current no-module-system source layout exposes all private declarations listed above to the imported environment. The check is meaningful kernel-axiom evidence, not a mathematical semantic review and not a hostile-toolchain/corrupt-olean detector.

`--skip-build` is expressly labelled as not certifying a fresh build and records `full_build_in_this_run = false` with a null build exit code. The current released record uses the full-build mode.

## Configuration and reproduction

The package's Lean options agree with the configuration template: autoImplicit=false, the established transparency setting, and increased synthesis heartbeats. `lean-toolchain` pins 4.32.1. The root manifest records the two local path dependencies, their relative sibling dependencies, and fixed transitive Git revisions. README correctly instructs preserving the geometry repository's original relative layout of the geometry libraries and shared package, rerunning configure and `lake update`, and using the same external toolchain's lake for update and verification. Reconfiguration necessarily changes local-path configuration hashes; an independently reproduced release record should bind the new configuration rather than match the original machine's path bytes.

The fingerprint algorithm deterministically hashes sorted relative Lean-source paths and file contents, excluding hidden/cache trees. Its advertised scope is exact external Lean source trees, not every auxiliary file in the repositories or every transitive package. This matches its implementation.

## Concrete publication hardening suggestions

The mathematical build/axiom evidence passes the checks above. The following small metadata/workflow improvements should be addressed or explicitly documented before presenting the scripts as automatically enforcing all pinned inputs:

1. `configure.py` validates directory markers and Lean-toolchain text only. Its commit IDs are help text, not checked revisions. The present lakefile comment “The bootstrap script checks their exact source revisions” is inaccurate for this script. Remove that comment or add real enforcement; put the existing dependency fingerprint `--check` in the main reproduction command sequence before building.
2. `verify.py` does not itself check the actual executed Lean version or the saved dependency fingerprints. A different explicitly passed lake executable or changed dependency checkout could produce a fresh passing build whose JSON still records only the source `lean-toolchain` file. Consider recording/validating `lake env lean --version` and invoking fingerprint checks based on the resolved dependency paths, or clearly retain these as mandatory prerequisite checks in README.
3. `release-check.source_sha256` currently binds all mathematics, Audit.lean, lakefile.lean, manifest, and lean-toolchain, but not the three release scripts or dependency-fingerprints.json. Including those files would also bind the exact verification procedure and dependency record. Documentation/archive hashes can be managed separately by the packaging step.

These suggestions do not invalidate the present same-source 757-declaration proof audit. They improve reproducibility of the published checking procedure. The root agent was informed; I did not modify implementation files.


## Addendum: strengthened release entry point

The parent implemented the three hardening suggestions. I reread the updated scripts/configuration/README without changing them or rerunning the build.

Reviewed `scripts/verify.py` SHA256:
`9a8390f4d2e47473b676b285ce25411d334eb2e38bad5b17a9352dd1027d50fb`.

**Source-review verdict: pass; all three earlier publication suggestions are resolved.**

- The verifier runs the actual `lake env lean --version`, requires the exact 4.32.1 version token (not a 4.32.10 prefix match), and records the complete stdout version string.
- It reads the actual Lake manifest, requires local path packages for mathlib, the Ricci-flow library, DoCarmoLib and Shared, and checks the geometry siblings against the resolved upstream repository layout. The fingerprint command therefore checks the dependencies selected by this project rather than independent user-supplied lookalike directories. A failed mandatory `--check` exits before building.
- The release hash set now includes every existing release `.py` script and the dependency fingerprint baseline as well as the prior mathematics, audit, toolchain and Lake files. It compares those bytes before and after the build/audit and refuses to issue a passing new release record if they changed. Expected source-module coverage is still checked after the audit.
- README now accurately states that configure validates layout/toolchain labels but does not itself verify Git revisions; verification enforces the saved source fingerprints. The inaccurate lakefile bootstrap comment was replaced with the correct verifier description.

The stronger checker still labels skip-build mode accurately and keeps semantic review separate. No new mathematical or axiom assumptions were introduced. Dependency fingerprint verification occurs before the build; the documented source-unchanged guarantee concerns the hashed project/configuration files, not concurrently mutated external dependency trees. The ordinary frozen-checkout release procedure satisfies this scope.

At the time of this read-only review, the parent-reported enhanced full verification was still running and the old release record remained in place. Accordingly this addendum certifies the amended checking source, not completion of that in-flight run. Once it exits successfully, the new release record should contain `lean_executable_version`, `dependency_fingerprint_check_exit_code = 0`, `source_unchanged_during_verification = true`, and hashes for the release scripts/baseline; those fields distinguish it from the previous record.
