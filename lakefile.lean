import Lake
open Lake DSL

package CurveControl where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

-- Local, pinned checkouts are shared to avoid duplicate dependencies.
-- scripts/verify.py compares dependency Lean sources with the saved fingerprints.
require mathlib from "../../work/lean-deps/mathlib4-520045ab"
require MorganTianLib from
  "../../work/poincare-duplicate-audit/sources/frenzymath__Poincare-Conjecture/formalized-sources/MorganTian"

@[default_target]
lean_lib CurveControl
