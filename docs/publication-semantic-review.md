# Publication semantic review

Date: 2026-09-09. Reviewer: the independent `curve_control_specification` agent. This is a semantic review of the publication text and blueprint data, not external human peer review. The reviewer did not author the paper's initial draft. The original 21-node blueprint was prepared by this reviewer; its added application node and revised mappings were supplied by the main agent and are explicitly rechecked here.

## Reviewed versions

| Artifact | SHA-256 |
|---|---|
| `paper/curve-estimates.tex` | `67102496624ce37882d1c43f16b61094b152a7b55ed06fa35d944b7501257020` |
| `blueprint/blueprint.json` | `e6f51786e259e2941983cd566223287d2bdade938612b95372f992ba023b4a0f` |

The corresponding new example is `CurveControl/Examples/StaticFactorApplication.lean`, SHA-256 `4f282888c9e432a824dd6bed822e73359fb6c70623a44cd7049edc9987e4b141`, inspected earlier for its statements. Independent proof review of that example and complete release-tool verification are separate evidence owned by their assigned agents.

## Verdict

**Accept these two publication artifacts at the hashes above. No mandatory mathematical correction remains.** The paper's earlier required corrections R1 and R2 have been made, and the new application node correctly describes the actual constructed scaled-metric interface. This judgment concerns mathematical meaning and code mapping; it does not claim another full build or another PDF visual review.

## Paper corrections verified

- The positive-scale discussion now states that the example constructs the genuine metric (h_\lambda=\lambda^2h_*), proves the actual tangent-norm scaling, and supplies uniform full-interval bounds. It no longer assigns construction of the scaled metric family to the caller. A concrete AddCircle atlas and its starting metric, actual smooth curve-flow existence, ramps and initial bounds remain correctly outside that construction.
- The limitations paragraph has removed “scaled factor objects” and retained “concrete circle atlases and their starting metrics”. This distinguishes the newly constructed arbitrary-metric scaling from an unimplemented concrete circle atlas.
- The appendix quantifier display now separately quantifies (\ell\in\Lambda), (i\in\mathcal I), and (t\in[a,b]). It no longer places the two index types in the time interval.
- The explicit-bound theorem now states that the ambient bound constants are nonnegative. The energy proposition explicitly defines unit vectors by (g(t)(V,V)=1), matching the actual Lean hypothesis over every point and time. The product-model paragraph uses the L² type `WithLp 2` on the mathematical product (E\times F), rather than misleading executable-looking `E * F` syntax.

The main theorem retains the correct order: first constants depending on the compact base flow and time interval, then arbitrary external indices, static one-dimensional factor metrics, curve families and initial bounds. Initial total curvature and length both appear in the final coefficient. The paper consistently distinguishes actual geometry roots from conditional scalar interfaces and distinguishes the regularized comparison route from an unimplemented unregularized Θ local-AC/a.e. theorem.

The corrected evolution signs, spatial projection, metric-variation term, fixed-chart connection derivative, endpoint convention, accumulated-energy weights and actual product tensor interpretation remain consistent with the prior semantic review. No new mathematical discrepancy was found.

## Blueprint additions verified

The blueprint now has **22 nodes and 62 declaration mappings**. The new `scaled_factor_application` node maps the seven exact declarations in `CurveControl.Examples.StaticFactorApplication`:

- `scaledFactorMetric`
- `scaledFactorMetric_inner`
- `scaledFactorMetric_norm`
- `scaledFactorMetric_static`
- `scaledProduct_isRicciFlow`
- `exists_scaledFactor_curve_bounds`
- `exists_scaledFactor_fullInterval_bounds`

The formula (h_\lambda=\lambda^2h_*) and norm formula apply to positive λ. The full-interval bounds use (b-a), not (t-a), consistently with the final example theorem. They follow from the nonnegative exponential coefficients and actual nonnegative initial quantities once a particular curve is selected. No positivity or existence of a curve is inferred from an empty index family.

The displayed formula is a mathematical summary rather than the full Lean type. Its explanation, dependency on `uniform_product_estimate`, and explicit caveats correctly supply the context: compact base Ricci flow, given actual one-dimensional factor and starting metric, existing smooth immersed periodic curve flows and common initial bounds. It neither extends the metric to λ=0 nor requires uniform positive lower scale or index regularity. In the actual theorem the constants precede even the starting metric (h_*), hence the stated scale independence is justified.

The additional `chartChristoffelContraction_productL2` mapping in `product_curvature_ricci` is real and appropriate to the node's explanation of the connection-to-curvature proof. No arbitrary connection-splitting assumption is introduced by that mapping.

All 62 blueprint declaration strings and all **21 paper `leanref` pairs** were checked against their exact modules' current compiled audit inventories; none was missing. The narrative dependency graph is acyclic. These checks validate the publication mapping; they do not substitute for the separately run Lean environment checker. Blueprint dependencies remain explicitly mathematical exposition prerequisites, not claims of exhaustive Lean constant dependencies.

## Claims and publication scope

The paper expressly makes no claim of a new mathematical estimate or priority of formalization, identifies AI assistance and AI semantic reviews, and does not call them external human peer review. It describes an unsigned review draft and does not claim acceptance by an external mathematical team. It does not claim to prove flow existence, continuation, finite extinction, or the entire Poincaré conjecture. Its title's finite-extinction wording is qualified as a module/interface for that argument.

The bibliography's primary metadata was checked in the preceding paper review and is not changed by these corrections. Artifact-level build, source fingerprint and axiom claims should remain bound to the final release record as the main agent regenerates publication outputs. A change to either reviewed source hash calls for checking the changed portions before carrying this acceptance forward.
