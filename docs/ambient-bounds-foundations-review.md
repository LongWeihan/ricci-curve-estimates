# Ambient bounds foundations — independent semantic review

Review date: 2026-09-09. Reviewer: weighted_integral_proof subagent.
This review is read-only with respect to Lean sources. It checks statement meaning and proof dependencies, not merely elaboration. The parent supplied the separate compilation/public-declaration axiom-audit evidence; this review does not claim a new compilation run.

## Frozen sources reviewed

| File | SHA256 |
|---|---|
| Geometry/ChartNormControl.lean | `849c299bcc8fc94e970ae9f1265828bc3599b59a6fff1f95b82d33d25d86de89` |
| Geometry/AmbientTensorRegularity.lean | `328287fa2da56e3a8b9551276bd9d047834775c939ba84e2c34f52b601f20596` |
| Geometry/AmbientTensorExpansion.lean | `d061b5f32e90581d464ca63acac1c90f1a74cb54cf3cdb7f394e2cc13db79c83` |

Verdict for these three frozen files: **semantic pass**. No model-norm/metric-norm substitution, unproved tensor-continuity hypothesis, assumed projection norm bound, or illicit time-endpoint extension was found. This verdict does not yet certify a global compact ambient-bound constructor.

## ChartNormControl

The frame is the genuine transported finite basis `chartBasisFamily α hp`, at the tangent fiber over `p`. Its parameter `hp` is membership of that same point in the tangent trivialization base set at the fixed chart center `α`. The reviewed upstream `chartBasisFamily_apply` identifies these basis vectors with `chartBasisVecFiber α i p`; the proof does not identify the frame with a metric-orthonormal frame.

The matrix is the actual Gram matrix for this frame and the actual metric `g` at `p`. Its inverse is `chartInvGramMatrix = chartGramMatrix⁻¹`. The upstream inverse identity used here requires `hp` and proves invertibility from positive definiteness of this Gram matrix. No unconstrained off-chart value of the matrix inverse is used in a bound.

`chartMetricDual` uses row `i` of the inverse Gram matrix. Matrix multiplication gives its metric pairing with basis vector `k` as δᵢₖ. Expansion of an arbitrary vector in the same basis then identifies that pairing with coordinate `i`. Pairing the dual vector with itself gives the inverse Gram diagonal entry. In particular diagonal nonnegativity is derived from metric positivity; it is not assumed or inferred from the model-space inner product.

The final estimate is exactly

`|b.repr v i| ≤ sqrt(invGram i i) * sqrt(g.metricInner p v v)`.

Its Cauchy–Schwarz step uses the reviewed `metricInner_sq_le`, which is proved from positivity of `g` applied to `W − c V`. `AmbientBounds.metricNorm` unfolds to the last square root. Thus the model-space `InnerProductSpace ℝ E` only supports the existing coordinate machinery; its norm is not substituted for the metric norm of a tangent vector. No tangent projection is used.

## AmbientTensorRegularity

The input `IsSmoothMetricFamilyOn g J` is the upstream definition asserting within-smoothness of the actual horizontal metric section on `M × J`. It is not a packaged tensor-continuity conclusion. Ricci coefficient smoothness is obtained from existing joint Christoffel/curvature coefficient proofs; covariant Ricci adds an actual spatial derivative and the two Christoffel correction sums.

The auxiliary `contDiffOn_spatialFDeriv_apply` keeps the original arbitrary time set `J`. It introduces a second, independently varying spatial argument on open `U`, differentiates only that argument using `U.uniqueDiffOn`, and changes `fderivWithin` to `fderiv` only because the spatial target is open and the evaluation point lies in it. It never asserts that `J` is open, never replaces a within time derivative by an ambient time derivative, and does not require a time extension at either endpoint. The function is smooth along `J × U`, exactly as needed for compact closed-time rectangles.

`actualCovRicci` fixes the canonical Levi-Civita connection of `g` and supplies its proved Levi-Civita property through the Koszul-dual theorem. The three slots are, in order, the differentiation direction and the two Ricci arguments. The fixed-chart coefficients evaluate this intrinsic tensor on three chart-frame vectors at the single point `(extChartAt I α).symm y`.

The bridge to `chartCovRicciOnE` explicitly requires `y` in this chart target. The reviewed upstream proof obtains local chart vector fields and proves the derivative/Christoffel identity there. Consequently chart junk values outside the target cannot supply a false continuity argument. The analogous actual Ricci bridge evaluates the genuine Ricci tensor on two vectors of that same frame. Smoothness and continuity of these actual coefficients are conclusions.

The `SigmaCompactSpace M` and `T2Space M` assumptions used in the intrinsic section are explicit prerequisites of the upstream global-extension construction of tensor values; they do not encode an ambient tensor bound.

## AmbientTensorExpansion

The general trilinear and quadrilinear lemmas are exact expansions in an arbitrary finite algebraic basis. Each coefficient is the matching component of the corresponding vector, and the tensor is evaluated on the same ordered basis slots. The finite-sum permutations reorder the sums without changing a tensor slot or assuming symmetry.

`covRicciTrilinear` is built from the existing actual covariant Ricci bilinear tensor and the proved additivity/homogeneity in its direction slot. Its application theorem is definitional. The resulting expansion is therefore for `(∇_u Ric)(v,w)`, not an auxiliary scalar function.

`curvatureQuadrilinear` curries the actual Morgan–Tian `curvatureFormAt` using its proved linearity in all four slots. Its application theorem is also definitional. The expansion preserves that source's curvature convention; no sign conversion or curvature symmetry is silently assumed. It accepts any connection because multilinearity itself does not require Levi-Civita; the later actual ambient-bound application must supply the canonical metric connection.

These are expansion equalities, not norm estimates. Neither a model-space operator norm nor a presumed bound on any projection occurs.

## Obligations reserved for CompactAmbientBounds

The three passing files are sufficient foundations, not the final compactness argument. The later frozen constructor must still be checked for all of the following:

1. Compact chart pieces must lie in the matching fixed chart target/base set, and the finite covering must cover the requested whole spatial compact set. Each piece must be paired with the entire closed time interval, so the resulting constants are simultaneous in time and point.
2. The inverse Gram factors must obtain genuine joint closed-time continuity and boundedness from the metric family; fixed-time smoothness alone is insufficient for a single time-uniform coordinate constant.
3. Coefficient bounds for the four-linear expansion must concern the fully covariant `curvatureFormAt` evaluated on the frame. Raw Christoffel curvature coefficients with one raised index cannot be inserted without the explicit metric lowering factor/bridge.
4. The three-/four-fold finite sums must include all coordinate factors and the correct dimension multiplicity, with nonnegative constants when monotonicity is used.
5. Every local bound must be transported to the same point, chart frame, actual metric and canonical Levi-Civita connection used by the final intrinsic predicate. The maximum/sum over the finite cover must dominate every local constant, including any empty-index or dimension assumptions.
6. No continuity of a tensor norm and no norm of a chart projection may be added as a caller assumption. The coordinate-dual bound above is the available proved bridge.

CompactAmbientBounds is still under development at the time of this report. Its review will be appended only after a frozen source hash is provided.


## Addendum: frozen CompactAmbientBounds review

Reviewed source: `Geometry/CompactAmbientBounds.lean`, SHA256
`5df639fb3f8fb7743219102ad67efb1ea767b3001d295db2cb910757cf255e89`.
The source hash was independently read and matched the frozen hash. The author reports 17 public declarations with only the standard three axioms and a generated olean; the parent is running the separate strict audit. This addendum is the independent semantic review of the implementation.

**Verdict: semantic pass. Recommend accepting the ambient-uniformity construction once the same-hash strict audit is confirmed.** All six previously reserved obligations are discharged by this source and its checked dependency bridges. No additional caller tensor-continuity, tensor-bound, projection-bound, or Ricci-flow-PDE premise was introduced.

### Joint coefficient bounds, including closed-time endpoints

`exists_bound_finite_family` first proves continuity of the finite coordinate tuple, applies compact boundedness to that real-valued finite tuple, and takes `max C 0`. The use of its finite Pi norm is solely a bound on a finite list of scalar tensor coefficients. It is not an identification of a tangent-vector model norm with a Riemannian metric norm.

The four compact-box coefficient theorems apply this lemma on exactly `Icc a b × L`. They restrict previously proved joint within-continuity on `J × chartTarget` using the supplied inclusions. Consequently one constant controls every requested time, every point of the box, and every tensor index simultaneously. No separate pointwise-in-time supremum is substituted for a uniform constant.

In particular the inverse-Gram theorem calls the actual joint theorem `contDiffOn_chartInvGramOnE_timeSpace`. I checked this dependency in `MetricCoordinateVariation.lean`: it starts from actual joint Gram coefficients, builds determinant and adjugate smoothness, and uses nonvanishing of the positive-definite Gram determinant on the chart. Thus the inverse-coordinate factors genuinely have closed-time regularity; fixed-time smoothness is not being reused as a joint conclusion.

The new `contDiffOn_chartRiemannCoefOnE_timeSpace` explicitly lowers the mixed curvature output index by summing `chartCurvatureCoef * chartGramOnE`. I checked the upstream definition and equality bridge in `RiemannVariation.lean`: this is the actual `(0,4)` form `curvatureFormAt g g.leviCivitaConnection` on the chart frame, with the same ordered slots. It is not the unlowered `(1,3)` coefficient. The covariant Ricci coefficient bound uses the earlier reviewed spatial-derivative/Christoffel proof, retaining the arbitrary time set and its endpoints.

### Local intrinsic estimates and dimension factors

`sum_abs_chartBasis_repr_le` applies the previously proved metric-dual coordinate estimate to each of the `n = finrank ℝ E` coordinates. Bounding every inverse-Gram diagonal by `A` gives the explicit factor `F = n * sqrt A` in the ℓ¹-coordinate bound. Nonnegativity of `sqrt A` and the actual metric norms justifies each multiplication. No coordinate projection operator norm is assumed.

`tensorBoundsAt_of_chart_coefficients` uses actual expansions of Ricci, Riemann, and covariant Ricci and then repeated absolute finite-sum estimates. Every tensor slot contributes one ℓ¹-coordinate factor. Hence the resulting constants are precisely `B*F²`, `K*F⁴`, and `D*F³`, respectively. The powers and dimension multiplicities match the two-, four-, and three-linear tensors. Nonnegative coefficient constants and metric norms are available before the monotonicity steps, and the concluding ring rearrangements preserve all factors.

`exists_tensorBounds_on_compact_chart` evaluates these bounds at an actual point `p` in the source of the same fixed chart. It derives the matching tangent-trivialization membership, proves the coordinate lies in the target, and uses the chart left inverse to recover `p`. It then rewrites each coefficient with the actual Ricci/Riemann/covariant-Ricci frame equality and `chartBasisFamily_apply`. The norm bound therefore refers to the same fiber, metric, basis, and canonical Levi-Civita connection as `AmbientBounds.TensorBoundsAt`.

### Finite chart cover and global constants

For every chart center `p`, the proof chooses a positive-radius open model ball inside that chart target. The local compact box is the closed ball of half that radius, still inside the same target; finite-dimensional properness supplies its compactness. Its associated open manifold neighborhood is the chart source intersected with the inverse image of the corresponding open half-radius ball. The center belongs to this neighborhood, and every point in it maps into the closed box.

Compactness of the whole manifold produces a finite subcover of these genuine open neighborhoods. Thus the selected spatial chart cover is fixed independently of time, and each selected box already carries constants for the entire closed interval. The argument does not attempt to use a compact chart target or assume that a chart source itself has compact closure.

The global constants are finite sums of the nonnegative local constants. `Finset.single_le_sum` proves each selected local constant is dominated by its global sum. At every point the cover supplies a selected chart, and `tensorBoundsAt_mono` increases its local intrinsic constants to the global ones using nonnegativity of all metric norms. The final proof also establishes global nonnegativity separately. Empty manifolds or empty time intervals create only vacuous universal estimates; zero finite sums remain nonnegative. No missing point is hidden by an empty selected index set.

### Root scope and acceptance recommendation

The final theorem `exists_uniformTensorBoundsOn` takes only actual `IsSmoothMetricFamilyOn g J`, inclusion `Icc a b ⊆ J`, and `[CompactSpace M]`, in addition to the standing finite-dimensional smooth boundaryless Hausdorff/sigma-compact manifold and model-space assumptions explicitly present in the section. It produces nonnegative `B,K,D` and `UniformTensorBoundsOn g (Icc a b) B K D`, whose definition quantifies over every time in the interval, every spatial point, and all tangent vectors in every tensor slot.

No Ricci evolution equation is needed to obtain this compactness result; this is mathematically the expected stronger statement for arbitrary smooth metric families. The result constructs exactly the actual ambient tensor bounds needed by the curve-estimate layer. It certifies the environmental constant-selection component of uniformity. Any separate family-initial-data bound or product/ramp projection construction remains outside this review, rather than being implicitly certified here.
