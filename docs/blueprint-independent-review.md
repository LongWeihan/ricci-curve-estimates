# Independent blueprint semantic review

**Final result: PASS.** The sole condition-summary issue identified below has been corrected and independently rechecked.

Reviewed independently of the blueprint author against the exported full Lean types and corresponding source declarations. No mathematical rebuild was performed; build and whole-library axiom verification remain separate evidence.

## Reviewed versions

- Final accepted `blueprint/blueprint.json`: SHA256 `a50e6ca7f6cef9a042b062fef4e11ad8d646fde766e9053bd6aec2d30bce6e84`.
- Initially reviewed blueprint before the documented correction: SHA256 `e6f51786e259e2941983cd566223287d2bdade938612b95372f992ba023b4a0f`.
- `verification/blueprint-declarations.json`: SHA256 `6bde2b1e36866c42f9f8c9fad011aedb589e0a1bcb9f708bcbe001bf4c54dcf5`.
- Scope: all 22 exposition nodes and all 62 referenced declarations. References are unique, cover the 62 metadata records exactly, and match source modules and declaration names. No exported type contains `⋯`; no dependency target is missing. These checks do not identify exposition edges with kernel dependency edges.

## Finding and verified correction

The initial review identified one local condition-summary issue, now resolved:

**`length_energy.scope_caveats`** originally said “Only a lower bound on Ric(S,S) is needed for this branch.” Both exposed roots, `weighted_curvatureEnergy_integral_le` and `curvatureEnergy_integral_le` in `Geometry/LengthEstimates.lean:146` and `:164`, actually assume

`∀ t ∈ Icc a b, ∀ p V, g(t)(V,V) = 1 → −B ≤ Ric(g(t))(V,V)`.

Thus the exported interface requires a uniform lower bound on **all ambient unit vectors** throughout the interval. A bound only along the curve's unit tangent is mathematically sufficient for the underlying differential argument, but that weaker-interface theorem is not what these linked declarations expose. Suggested replacement:

> The exposed roots assume a uniform lower Ricci bound on all ambient unit vectors over [a,b]; no upper Ricci, Riemann-curvature or covariant-Ricci bound is required. The unweighted version requires B nonnegative.

The parent updated this caveat to: “The exposed roots assume a uniform lower Ricci bound on all ambient unit vectors over [a,b]; no upper Ricci, Riemann or covariant Ricci bound is required. The unweighted version requires B >= 0.” I independently read the final JSON and confirmed this text matches the exposed assumptions. The metadata hash is unchanged. This documentation correction requires no mathematical rebuild. No other material mismatch was found.

## Node-by-node coverage

| Nodes | Assessment |
|---|---|
| `flow_input`, `curve_geometry` | Actual Ricci flow is a separate upstream input; the curve predicate contains smoothness, immersion, period-one closure and the within flow equation, without evolution/estimate fields. Definitions use actual metric pairings and arclength density. Self-intersections and supplied existence are accurately disclosed. |
| `speed_evolution`, `connection_variation`, `curvature_evolution` | Formula coefficients and tensor slots match the full types. Classical time derivatives require interior time, as the global notation and input caveats state. Connection variation differentiates the spatial connection at a fixed chart point; metric lowering and the chart/intrinsic curvature sign are correctly distinguished. No higher-order endpoint evolution is advertised. |
| `spatial_kato`, `ambient_error` | The Kato result closes actual-flow regularity at interior times. The separate norm-decomposition lemma explicitly retains its covariant-differentiability condition in its exported type. Ambient bounds are actual multilinear evaluation bounds; their role as inputs at this layer is disclosed. The absolute error estimate and max-coefficient bound are compatible with the displayed formula. |
| `regularized_pde`, `moving_integrals` | The scalar lemma explicitly takes differentiability, positivity, Kato and scalar-PDE hypotheses; the caveat correctly explains that the geometric assembly discharges them. The displayed cubic term equals the Lean expression `sqrt(q)^3` for the nonnegative q in the interface. Periodic cancellation and moving-density integration concern fixed positive epsilon, not derivatives of unregularized total curvature. |
| `interior_comparison`, `epsilon_limit` | Interior derivative information plus closed-interval continuity supplies endpoint estimates. The regularization limit applies to compared values and does not interchange a limit with a time derivative. Absence of a general Theta absolute-continuity/a.e.-derivative theorem is explicit. |
| `actual_curve_estimate`, `length_energy` | The actual root consumes real flows and ambient bounds, not target PDEs. The family root initially bounds Theta+L; the final product result correctly uses common separate initial bounds to obtain its weaker Theta bound. Energy formulas and the B≥0 restriction are correct, with the lower-bound quantifier correction above now verified. |
| `compact_tensor_bounds` | Compactness of the base and actual joint smoothness supply finite coefficients over the closed interval. The displayed tensor norms are explicitly qualified as multilinear evaluation bounds. No compactness of the factor is asserted or required. |
| `product_metric`, `one_dimensional_flatness` | The Hilbert model change and actual fiber isometry are real constructions. One-dimensional vanishing holds for the supplied metric and the canonical/Levi-Civita connection as reflected in the full types. No circle atlas follows from dimension one. |
| `product_curvature_ricci`, `product_covricci` | Actual tensor splitting has no target splitting hypothesis. Coordinate results retain chart-target conditions; exposition states this domain. Component notation denotes the proved model projections, not a replacement of metric norms by model norms. |
| `product_ricci_flow`, `product_tensor_bounds` | The static one-dimensional factor yields actual product Ricci flow, including within endpoint equations. The three constants are inherited from actual base tensor bounds through vanishing and norm-decreasing projections. The exposition distinguishes supplied base bounds from their later compactness construction. |
| `uniform_product_estimate`, `scaled_factor_application` | Full types choose B,C before factor metrics, curve families and common initial bounds. The fixed factor manifold/model are outer parameters; the actual proof chooses coefficients from the compact base flow. The application constructs λ²h₀ and proves actual norm scaling by λ, for λ>0. Its fixed full-interval exponents follow from B,C≥0 and t≤b. Supplied one-dimensional geometry, existing smooth curve flows and uniform initial bounds remain inputs. No concrete circle, ramp, flow existence, scale-zero metric or convergence of flows is claimed. |

## Dependency and scope interpretation

The top-level `dependency_semantics` explicitly labels every edge as a curated, non-exhaustive mathematical exposition prerequisite, not a Lean constant-dependency edge. Some edges carry context rather than minimal logical prerequisites; this is consistent with that declared interpretation and is not presented as a kernel dependency audit.

The compact displays omit routine manifold typeclasses, while the linked full types retain finite-dimensional real inner-product models, applicable boundaryless assumptions, and separation/countability conditions. In this linked exposition these omissions are not claims of stronger generality. The critical analytic and geometric restrictions—existing flows, immersion, static one-dimensional factor, positive scale, common initial bounds, interior derivatives, endpoint continuity, and the AC/a.e. non-claim—are present across node explanations/caveats and global notation.

The single lower-Ricci-quantifier wording correction is verified in the final accepted JSON hash above. This review therefore passes with no remaining substantive objection to the blueprint. Only this review document was written; source, blueprint, metadata, configuration and dashboard were not modified by the reviewer.
