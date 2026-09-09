import CurveControl.Geometry.CurvatureGradient
import CurveControl.Geometry.AmbientBounds
import DoCarmoLib.Riemannian.TensorBundle.MusicalIso

/-!
# Controlling chart coordinates by the metric norm

The constant is the square root of an actual inverse Gram entry. This bridges
compact bounds on tensor coefficients to intrinsic bounds on tangent vectors.
-/

open Riemannian Riemannian.Tensor
open scoped Manifold ContDiff

noncomputable section
namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The metric dual of a chart coordinate functional. -/
def chartMetricDual (g : RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I p :=
  ∑ j, chartInvGramMatrix g α p i j • chartBasisFamily α hp j

theorem chartMetricDual_pairing_basis (g : RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i k : Fin (Module.finrank ℝ E)) :
    g.metricInner p (chartMetricDual g α hp i) (chartBasisFamily α hp k) =
      if i = k then 1 else 0 := by
  classical
  change g.inner p (∑ j, chartInvGramMatrix g α p i j • chartBasisFamily α hp j)
    (chartBasisFamily α hp k) = _
  simp only [map_sum, sum_apply, map_smul,
    smul_apply, smul_eq_mul, chartBasisFamily_apply]
  have h := congrArg (fun A => A i k) (chartInvGramMatrix_mul_chartGramMatrix g α hp)
  simpa only [Matrix.mul_apply, Matrix.one_apply, chartGramMatrix_apply] using h

theorem chartMetricDual_pairing (g : RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I p) :
    g.metricInner p (chartMetricDual g α hp i) v = (chartBasisFamily α hp).repr v i := by
  classical
  let b := chartBasisFamily (I := I) α hp
  calc
    _ = g.inner p (chartMetricDual g α hp i) (∑ j, b.repr v j • b j) := by
      rw [b.sum_repr]
      rfl
    _ = ∑ j, b.repr v j * (if i = j then 1 else 0) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact chartMetricDual_pairing_basis g α hp i j
    _ = b.repr v i := by simp

theorem chartMetricDual_sq (g : RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    g.metricInner p (chartMetricDual g α hp i) (chartMetricDual g α hp i) =
      chartInvGramMatrix g α p i i := by
  classical
  rw [chartMetricDual_pairing]
  simp [chartMetricDual, map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply]

theorem chartInvGramMatrix_diagonal_nonneg (g : RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) : 0 ≤ chartInvGramMatrix g α p i i := by
  rw [← chartMetricDual_sq g α hp i]
  exact g.metricInner_self_nonneg p _

/-- **Math.** Every chart coordinate is bounded by an explicit inverse-Gram factor times
the actual metric norm, rather than the model-space norm. -/
theorem abs_chartBasis_repr_le (g : RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I p) :
    |(chartBasisFamily α hp).repr v i| ≤
      Real.sqrt (chartInvGramMatrix g α p i i) * AmbientBounds.metricNorm g p v := by
  have h := metricInner_sq_le g p (chartMetricDual g α hp i) v
  rw [chartMetricDual_pairing, chartMetricDual_sq] at h
  have hs := Real.sqrt_le_sqrt h
  simpa only [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (chartInvGramMatrix_diagonal_nonneg g α hp i),
    AmbientBounds.metricNorm] using hs

end CurveControl.Geometry
