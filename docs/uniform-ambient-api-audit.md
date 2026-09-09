# Uniform ambient constants / flat auxiliary circle: local source audit

Date: 2026-09-09. Read-only audit of existing sources; this report is the only file written. No downloads, installation, library compilation, or code/config/dashboard changes.

## Evidence scope and verdict

- Mathlib root `L = /Users/bytedance/Documents/Codex/2026-09-09/wo/work/lean-deps/mathlib4-520045ab/Mathlib` (the requested pinned source directory).
- Existing frenzy source root `F = /Users/bytedance/Documents/Codex/2026-09-09/wo/work/poincare-duplicate-audit/sources/frenzymath__Poincare-Conjecture/formalized-sources`.
- Below, `D = F/DoCarmo/DoCarmoLib`, `M = F/MorganTian/MorganTianLib`. Paths and line numbers refer to this local snapshot, not live GitHub.
- “Source proof present” means the declaration body was inspected and is a definition or actual proof. It does NOT mean this audit compiled the declaration or checked its transitive axioms. No item below is newly verified by Lean in this audit.
- Conclusion: useful metric, connection, Ricci/covRicci, coordinate smoothness, tensor norm, compactness and circle-topology building blocks exist. I did not locate an end-to-end theorem deriving all three ambient bounds from a smooth compact base flow, nor an intrinsic product-metric/LC/Rm/Ric/covRic splitting API for `M × AddCircle λ`. These remain mathematical construction tasks, not configuration tasks.

## 1. Smooth compact base: actual APIs and missing bridge

| Local path:line | Actual declaration and assumptions | Status/use |
|---|---|---|
| `L/Geometry/Manifold/VectorBundle/Riemannian.lean:244` | `Bundle.ContMDiffRiemannianMetric`; fields `inner`, `symm`, `pos`, `isVonNBounded`, `contMDiff` | Actual metric data, not a curvature estimate. Smoothness is bundle-section smoothness. |
| `D/Riemannian/Metric/RiemannianMetric.lean:42` | `RiemannianMetric I M` aliases the smooth tangent-bundle metric; `metricInner` at 86 | Existing geometry representation to reuse. |
| `M/Ch03/RicciFlow/Basic.lean:100` | `IsSmoothMetricFamilyOn g J`: joint smoothness of horizontal metric section on `univ ×ˢ J`; `IsRicciFlowEquationOn` at 108 specifies the within-time derivative `-2 Ric`; `IsRicciFlowOn` at 115 adds interval/nontriviality | Appropriate geometric hypotheses; it does not assume curvature upper bounds. Spatial smoothness of each `g t` alone is insufficient to replace this joint hypothesis. |
| `M/Ch03/RicciFlow/ScalarSpacetimeSmooth.lean:140,160` | `contDiffOn_chartCurvatureCoef_timeSpace`, `contDiffOn_chartRicciCoefOnE_timeSpace`, from `IsSmoothMetricFamilyOn g J`, chart center and finite basis indices, on `J ×ˢ chart.target` | Source proofs present. Strong local starting point for joint scalar norm continuity; coordinate coefficients are not themselves invariant tensor norms. |
| `M/Ch03/RicciFlow/RicciEndomorphismContinuity.lean:89` | `ricciEndomorphismAt_continuousOn_of_isSmoothMetricFamilyOn`: fixed `p`, operator in the fixed tangent-fibre/model norm continuous in time | Source proof present, but fixed-point continuity does not yield joint compact-space-time boundedness or metric-varying intrinsic norm continuity automatically. Assumptions include finite nonzero dimension, complete model inner product, boundaryless smooth manifold, sigma-compact and Hausdorff. |
| `M/Ch03/RicciFlow/ShiGeometricLevels.lean:82,90,176` | `covTensorNormSqAt` = finite sum of squared orthonormal components; `covTensorNormAt` = square root; `riemannCovDerivNormAt g n p` = norm of `riemannCovDerivTower g n` | Actual norm definitions. Need basis-independent/chart-contraction bridge and joint continuity before applying compactness; arbitrary pointwise orthonormal basis choices cannot simply be asserted continuous. |
| `M/Ch03/RicciFlow/ScalarEvolution.lean:80` | `ricciNormSqAt`: trace of the squared Ricci endomorphism with the metric bundle instance installed | Actual definition, not existence of a uniform bound. |
| `L/Analysis/Normed/Group/Bounded.lean:96` | generated additive theorem `IsCompact.exists_bound_of_continuousOn`: compact `s`, `ContinuousOn f s` imply `∃ C, ∀ x∈s, ‖f x‖ ≤ C` | Source proof present (`to_additive` from primed multiplicative declaration). Apply to scalar invariant norms once continuity is proved; no nonempty hypothesis required. Enlarge C by `max C 0` or `max C 1`. |
| `L/Topology/Compactness/Compact.lean:1062` | `IsCompact.prod` | Builds compact `univ ×ˢ Icc a b` from compact base and compact interval. A singular endpoint is not covered unless smoothness there is actually supplied. |

Important distinction: `M/Ch03/RicciFlow/ShiAllOrderUniformComponents.lean:88` and `:119` really have proof bodies producing uniform derivative-norm constants, but their input is a family `RiemannianShiTowerCertificate`, not just smoothness plus compactness. The certificate at `M/Ch03/RicciFlow/ShiAllOrderBridge.lean:33` includes a pre-existing zeroth curvature bound `hw0` (:53), continuity of a combination (:60), a spatial maximum rule (:65), a Laplacian combination identity (:72), and differential tower inequalities (:76). Its positive cutoff `tau` also excludes time zero. Do not cite these consumers as already deriving the required compact-base ambient constants. Likewise `ShiNormBounds.lean:79` assumes the squared bound it converts to a norm bound.

For the requested short smooth compact time interval, the economical route is continuity + compactness, not re-proving or assuming Shi estimates. A direct joint norm-continuity theorem for `∇Ric` was not located in this bounded search.

## 2. Intrinsic connection and tensors: reusable, but no product split established

- `D/Riemannian/Manifold/DoCarmoCh2.lean:1191`: `RiemannianMetric.leviCivitaConnection`, constructed from Koszul/Riesz, with finite nonzero-dimensional inner-product model, sigma-compact Hausdorff manifold (plus surrounding smooth-manifold context). Source construction present.
- Same file :320: `leviCivita_unique g hext n₁ n₂ h₁ h₂`; given smooth extension of every tangent vector and two Levi-Civita proofs, gives connection equality. The extension-supported specialization is at :341. This is a useful route to certify a constructed product connection; it does not construct one.
- `M/Ch03/RicciFlow/MetricDistortion.lean:34`: `canonicalLeviCivita_isLeviCivita`; source proof identifies the canonical connection as LC.
- `M/Ch03/RicciFlow/Basic.lean:43`: `ricciTensorAt`, built from the actual canonical LC algebraic curvature form.
- `D/Riemannian/Connection/CurvaturePointwise.lean:271`: `AffineConnection.curvatureFormAt`, metric pairing of curvature operator; extension computation theorem at :276.
- `M/Ch01/PointwiseCurvature.lean:248`: another `curvatureFormAt` via global extensions. Avoid mixing these similarly named interfaces without the actual bridge theorem.
- `M/Ch01/RicciDivergence.lean:116`: `covRicci g nabla hLC U X Y`, the covariant derivative, not an arbitrary supplied tensor. :554 proves extension invariance, :583 defines `covRicciAt`, :588 relates it to smooth fields; :595/:607/:619/:631 provide pointwise linearity. Assumptions include boundaryless, finite nonzero-dimensional smooth manifold, sigma-compact/Hausdorff context. These are usable building blocks for a covariant 3-tensor norm.

Search found no actual constructor named/product-equivalent to `RiemannianMetric.prod` / `productMetric` / `prodMetric`, nor the requested LC/Rm/Ric/covRic splitting in the audited DoCarmo/MorganTian sources. This is a bounded search finding, not a theorem that no differently named API exists.

False friend: `M/Ch03/RicciFlow/GeneralizedProduct.lean:107` is `ProductGeneralizedRicciFlow g J`, a PROP recording the SAME ordinary flow smoothness/equation on horizontal tangent fibres of `M × ℝ`. The :118 conversion merely copies `hflow` fields; :176 returns `h.ricci_equation`. It does not equip the full product tangent bundle with `g ⊕ ds²`, and proves no spatial product curvature splitting. “Product” here is time-space packaging, not the auxiliary-circle product.

## 3. AddCircle λ: topology and metric ingredients, not flat Riemannian geometry yet

- `L/Analysis/Normed/Group/AddCircle.lean:43`: normed additive group instance on `AddCircle p` (quotient distance).
- :68 `norm_eq`: `‖(x : AddCircle p)‖ = |x - round (p⁻¹*x)*p|`.
- :107 `norm_coe_eq_abs_iff`, `p ≠ 0`: equality with `|x|` iff `|x| ≤ |p|/2`. This supplies the local Euclidean metric calculation, but is not a charted smooth metric or LC theorem.
- `L/Topology/Instances/AddCircle/Real.lean:33`: `AddCircle.compactSpace` under `[Fact (0 < p)]`.
- `L/Topology/Covering/AddCircle.lean:28,32,35`: quotient covering map and local homeomorphism under discrete topology on `zmultiples p`; the real positive-period specialization must instantiate that hypothesis.

No `AddCircle` occurrence was found in pinned `Mathlib/Geometry`, or in the audited DoCarmo/MorganTian Lean files. Thus the located evidence does not establish a smooth one-dimensional `AddCircle λ` Riemannian metric, its LC formula, or vanishing curvature. Building an atlas from local quotient lifts with translation transitions and the induced metric is a genuine outstanding step. A metric-space quotient and compactness alone do not provide these objects.

Convention must be explicit: `AddCircle λ` uses period/circumference λ. A circle of radius λ instead has circumference `2πλ`, or uses a fixed circle with a scaled metric. Do not silently interchange the parameter conventions.

## 4. Minimal construction order preserving full λ-uniform scope

1. Fix time slab `[a,b]` on which the original smooth flow is actually defined. Reuse canonical metric/LC/Ric/Rm/covRic definitions. Prove joint continuity of the scalar invariant norms using local coordinate contractions with inverse Gram matrix and derivatives; handle tensor norms independently of chosen orthonormal frames. Apply compactness on the BASE only to obtain finite nonnegative constants for Ric, Rm and ∇Ric.
2. Construct the smooth quotient circle for every positive period, its Euclidean local metric, and canonical LC; prove curvature zero from the actual definition (translation chart Christoffels zero, or intrinsic one-dimensional antisymmetry). Derive Ric and covRic zero. No assumed “flatness bound” as a replacement for this construction.
3. Construct the full product metric on tangent pairs, prove the norm-square sum and projection contraction. Construct product connection using local coordinate derivatives of arbitrary fields, check torsion-free/metric-compatible, identify it with canonical LC by uniqueness. Proving formulas only for lifted base fields is insufficient without extension to arbitrary tangent inputs.
4. Prove Rm/Ric/covRic tensor splitting from those definitions. Establish norm equality to the base tensor for zero-extended covariant tensors (or a proved dimension-only comparison). The projection contraction is the key to bounding arbitrary unit vectors with circle components.
5. Transfer the BASE constants: quantifier order `∃ C_Ric C_Rm C_dRic, ∀ λ>0, ∀ t∈[a,b], ∀ (x,θ), ...`. The constants are chosen before λ and may depend on the fixed base flow/time slab and dimension only. A weaker `∀ λ>0, ∃ Cλ` does not meet the requirement. Feed the established constants into the curve-family estimates; retain all curve and auxiliary-circle parameters.

Local quotient chart radii may shrink with λ. This is harmless for proving local tensor identities; it is NOT a source of a uniform injectivity radius. Never take compactness separately on each `M × AddCircle λ` and claim the resulting constants are λ-independent. No end-to-end uniform-ambient theorem has been proved by this audit.
