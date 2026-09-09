# Integrating the curve-estimate module

This guide accompanies the module by **GPT-6 Astra (AI model)** and **Juii-hang Leung (龙维汉)**. It separates supplied geometric objects from internally proved estimates. The [technical report](../paper/curve-estimates.pdf) supplies the mathematics and exact typeclass inventory; [reproduction](reproduction.md) supplies environment instructions.

## Choose an entry point

| Need | Fully qualified Lean declaration | Module |
|---|---|---|
| Existing curve flow with explicit genuine ambient bounds | `CurveControl.Geometry.IsCurveShorteningFlowOn.curve_estimate` | [CurveEstimates](../CurveControl/Geometry/CurveEstimates.lean) |
| Common initial bounds over any curve index | `CurveControl.Geometry.curve_family_uniform_estimate` | [CurveEstimates](../CurveControl/Geometry/CurveEstimates.lean) |
| Compact base and arbitrary static one-dimensional metric families | `CurveControl.Geometry.exists_uniform_static_product_family_estimate` | [UniformProductEstimates](../CurveControl/Geometry/UniformProductEstimates.lean) |
| Entire arbitrary positive-scale metric family | `CurveControl.Geometry.exists_uniform_positive_scale_product_estimate` | [UniformProductEstimates](../CurveControl/Geometry/UniformProductEstimates.lean) |
| Actual construction and estimates for `λ²h₀` | `CurveControl.Examples.StaticFactorApplication.exists_scaledFactor_curve_bounds` | [StaticFactorApplication](../CurveControl/Examples/StaticFactorApplication.lean) |
| One bound for all scales, curves and times | `CurveControl.Examples.StaticFactorApplication.exists_scaledFactor_fullInterval_bounds` | [StaticFactorApplication](../CurveControl/Examples/StaticFactorApplication.lean) |
| Accumulated curvature energy | `CurveControl.Geometry.IsCurveShorteningFlowOn.curvatureEnergy_integral_le` | [LengthEstimates](../CurveControl/Geometry/LengthEstimates.lean) |

## Caller contract

The final product interfaces use real finite-dimensional inner-product model spaces `E,F` of positive dimension, boundaryless models with corners `I,J`, and smooth charted manifolds `M,N`. Both manifolds are Hausdorff and sigma-compact; `M` is compact and `Module.finrank ℝ F = 1`. The actual product uses `productL2Model I J` and `productL2Metric I J`, so downstream curve types must use that model. The point set remains `M × N`.

Supply:

1. `hg : MorganTianLib.IsRicciFlowOn g (Set.Icc a b)` and `hab : a ≤ b`. The flow predicate includes joint within-smoothness, the actual Ricci equation, order-connectedness and nontriviality of the interval; thus the final root's interval is nondegenerate.
2. A genuine static factor metric, a family of such metrics, or the starting metric `h₀` for the scaled application. Supply the factor manifold and atlas independently.
3. The actual curves and `IsCurveShorteningFlowOn` for each. This predicate requires joint within-smoothness, period-one closedness, immersion, and the actual within-time equation `cₜ=H`. It is an existing solution, not an existence theorem.
4. Common initial bounds `L(a)≤L₀` and `Θ(a)≤Θ₀` for every scale and curve. The module does not construct these bounds from ramps or compact parameter families.

The final roots construct ambient constants from the compact base, prove actual product Ricci-flow status and tensor splitting, and derive the curve estimates internally. Do not provide curvature PDE, Kato, splitting, integral differentiation or final comparison hypotheses to these roots: none is needed.

## Concrete positive scaling

Import the application directly:

```lean
import CurveControl.Examples.StaticFactorApplication
```

In namespace `CurveControl.Examples.StaticFactorApplication`, `scaledFactorMetric h₀ ℓ` constructs a genuine metric for `ℓ : {r : ℝ // 0 < r}`. Its `scaledFactorMetric_inner` theorem gives multiplication of the bilinear metric by `ℓ.val ^ 2`; `scaledFactorMetric_norm` gives multiplication of actual tangent length by `ℓ.val`. Positivity, bounded-unit-ball structure and smoothness are proved in the constructor. `scaledProduct_isRicciFlow` then proves the time-static scaled product is a Ricci flow from the base equation and one-dimensionality.

`exists_scaledFactor_curve_bounds` chooses `B,C≥0` before `h₀`, the curve-index type, all curves and initial bounds. It yields

\[
L_{\lambda,i}(t)\le L_0e^{B(t-a)},\qquad
\Theta_{\lambda,i}(t)\le(\Theta_0+L_0)e^{C(t-a)}.
\]

`exists_scaledFactor_fullInterval_bounds` replaces `(t-a)` by `(b-a)` on the right, giving a single bound valid over the full closed interval. No lower bound on positive `λ` occurs. If `N` is a supplied smooth circle, these are its scaled metrics; this application does not construct a concrete `AddCircle` atlas or a ramp/curve solution.

## Lower-level reuse and conventions

For the non-product geometric root, `AmbientBounds.UniformTensorBoundsOn g T B K D` means bounds on the actual Ricci, Riemann and covariant Ricci tensors in their metric norms. The resulting coefficient is `C = max (6*B+2*K) (6*D) / 2 + B`. `curve_family_uniform_estimate` takes an initial bound `Q₀` for `Θ+L`, so use `Q₀=Θ₀+L₀` when starting with separate bounds.

The evolution uses a spatial time-dependent Levi–Civita derivative and includes the metric and connection time variations. The upstream do Carmo curvature sign is explicitly translated to the chart convention. Closed endpoints are handled by continuity and within-flow data; high-order classical derivatives are used at interior times. Total curvature is treated by comparing `Θε` and taking `ε→0`; no standalone unregularized `Θ` AC/a.e. interface is claimed.

Flow existence and continuation, concrete circle construction, ramp construction and the remaining finite-extinction proof remain upstream. Check the [release record](../verification/release-check.json) against the source files used for an integration. Human mathematical review of the caller's geometric representation and conventions remains distinct from the recorded AI semantic reviews and Lean proof checking.
