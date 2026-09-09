import CurveControl.Geometry.UniformProductEstimates

/-!
# Applying the curve estimates to an actual scaled static factor

Caller contract: supply an actual smooth one-dimensional manifold and an actual
Riemannian metric h₀ on it. This file constructs hλ = λ² h₀ for every positive
real λ, including its positivity, bounded-unit-ball and smoothness proofs.
If the supplied manifold is a smooth circle, this is its usual metric scaling.
No circle atlas, closed-curve immersion or curve-shortening-flow existence is
asserted by this example. Those are explicit geometric caller inputs.

The final theorem bounds length and total curvature simultaneously for every
positive scale, curve index and time in the full closed time interval. Its
constants are chosen from the compact base flow before the scale or curves.
-/
open Set Filter MeasureTheory Riemannian MorganTianLib
open scoped Manifold Topology ContDiff Bundle Interval
noncomputable section
namespace CurveControl.Examples.StaticFactorApplication
open CurveControl.Geometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

/-- **Math.** A positive real scale multiplies an actual metric by its square.
Every metric-structure field is constructed, not supplied as an assumption. -/
def scaledFactorMetric (h₀ : Riemannian.RiemannianMetric J N)
    (ℓ : {r : ℝ // 0 < r}) : Riemannian.RiemannianMetric J N where
  inner p := (ℓ.val ^ 2) • h₀.inner p
  symm p u v := by
    change ℓ.val ^ 2 * h₀.inner p u v = ℓ.val ^ 2 * h₀.inner p v u
    rw [h₀.symm]
  pos p u hu := by
    change 0 < ℓ.val ^ 2 * h₀.inner p u u
    exact mul_pos (sq_pos_of_pos ℓ.property) (h₀.pos p u hu)
  isVonNBounded p := by
    apply isVonNBounded_of_posDef (E := F)
    intro u hu
    change 0 < ℓ.val ^ 2 * h₀.inner p u u
    exact mul_pos (sq_pos_of_pos ℓ.property) (h₀.pos p u hu)
  contMDiff := h₀.contMDiff.const_smul_section

/-- **Math.** The constructed metric has the promised bilinear evaluation. -/
theorem scaledFactorMetric_inner (h₀ : Riemannian.RiemannianMetric J N)
    (ℓ : {r : ℝ // 0 < r}) (p : N) (u v : TangentSpace J p) :
    (scaledFactorMetric h₀ ℓ).metricInner p u v = ℓ.val ^ 2 * h₀.metricInner p u v := rfl

/-- **Math.** Scaling the metric by λ² scales actual tangent length by λ. -/
theorem scaledFactorMetric_norm [NeZero (Module.finrank ℝ F)] [J.Boundaryless]
    [SigmaCompactSpace N] [T2Space N]
    (h₀ : Riemannian.RiemannianMetric J N) (ℓ : {r : ℝ // 0 < r})
    (p : N) (v : TangentSpace J p) :
    AmbientBounds.metricNorm (scaledFactorMetric h₀ ℓ) p v =
      ℓ.val * AmbientBounds.metricNorm h₀ p v := by
  unfold AmbientBounds.metricNorm
  rw [scaledFactorMetric_inner, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ℓ.property.le]

/-- **Math.** Each constructed factor metric is static and smoothly constant
in Ricci-flow time, on any prescribed time set. -/
theorem scaledFactorMetric_static (h₀ : Riemannian.RiemannianMetric J N)
    (ℓ : {r : ℝ // 0 < r}) (T : Set ℝ) :
    IsSmoothMetricFamilyOn (fun _ => scaledFactorMetric h₀ ℓ) T :=
  isSmoothMetricFamilyOn_const J (scaledFactorMetric h₀ ℓ) T

variable [NeZero (Module.finrank ℝ F)] [J.Boundaryless]
  [SigmaCompactSpace N] [T2Space N]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The explicitly constructed scaled factor produces a genuine
Ricci-flow product whenever its real dimension is one. -/
theorem scaledProduct_isRicciFlow
    {g : ℝ → Riemannian.RiemannianMetric I M} {T : Set ℝ}
    (hg : IsRicciFlowOn g T) (hdim : Module.finrank ℝ F = 1)
    (h₀ : Riemannian.RiemannianMetric J N) (ℓ : {r : ℝ // 0 < r}) :
    IsRicciFlowOn (fun t => productL2Metric I J (g t) (scaledFactorMetric h₀ ℓ)) T :=
  isRicciFlowOn_productL2_oneDimensional I J hg (scaledFactorMetric h₀ ℓ) hdim

/-- **Math.** Concrete scaled-metric application. Exponential constants are
chosen from the compact base flow before h₀, the positive scale, curve indices
or initial bounds. Smooth immersed closed product-flow existence and the two
common initial bounds are the caller's only curve inputs. -/
theorem exists_scaledFactor_curve_bounds [CompactSpace M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {a b : ℝ}
    (hg : IsRicciFlowOn g (Icc a b)) (hab : a ≤ b) (hdim : Module.finrank ℝ F = 1) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (h₀ : Riemannian.RiemannianMetric J N) (ι : Type*)
        (c : {r : ℝ // 0 < r} → ι → ℝ → ℝ → M × N),
        (∀ ℓ i, IsCurveShorteningFlowOn (I := productL2Model I J)
          (fun t => productL2Metric I J (g t) (scaledFactorMetric h₀ ℓ)) (c ℓ i) (Icc a b)) →
        ∀ L₀ Θ₀ : ℝ,
          (∀ ℓ i, curveLength (productL2Metric I J (g a) (scaledFactorMetric h₀ ℓ))
            (c ℓ i a) ≤ L₀) →
          (∀ ℓ i, totalCurvature (productL2Metric I J (g a) (scaledFactorMetric h₀ ℓ))
            (c ℓ i a) ≤ Θ₀) →
          ∀ ℓ i, ∀ t ∈ Icc a b,
            curveLength (productL2Metric I J (g t) (scaledFactorMetric h₀ ℓ)) (c ℓ i t) ≤
              L₀ * Real.exp (B * (t - a)) ∧
            totalCurvature (productL2Metric I J (g t) (scaledFactorMetric h₀ ℓ)) (c ℓ i t) ≤
              (Θ₀ + L₀) * Real.exp (C * (t - a)) := by
  obtain ⟨B, C, hB, hC, hestimate⟩ :=
    exists_uniform_positive_scale_product_estimate I J (N := N) hg hab hdim
  refine ⟨B, C, hB, hC, ?_⟩
  intro h₀ ι c hc L₀ Θ₀ hL₀ hΘ₀
  exact hestimate ι (scaledFactorMetric h₀) c hc L₀ Θ₀ hL₀ hΘ₀

/-- **Math.** A downstream full-interval bound suitable for a later ramp
argument: one finite length bound and one finite total-curvature bound hold
simultaneously for all t, all curves and every positive scale, even as λ→0.
This is an estimate only; it does not assert ramp or curve-flow existence. -/
theorem exists_scaledFactor_fullInterval_bounds [CompactSpace M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {a b : ℝ}
    (hg : IsRicciFlowOn g (Icc a b)) (hab : a ≤ b) (hdim : Module.finrank ℝ F = 1) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (h₀ : Riemannian.RiemannianMetric J N) (ι : Type*)
        (c : {r : ℝ // 0 < r} → ι → ℝ → ℝ → M × N),
        (∀ ℓ i, IsCurveShorteningFlowOn (I := productL2Model I J)
          (fun t => productL2Metric I J (g t) (scaledFactorMetric h₀ ℓ)) (c ℓ i) (Icc a b)) →
        ∀ L₀ Θ₀ : ℝ,
          (∀ ℓ i, curveLength (productL2Metric I J (g a) (scaledFactorMetric h₀ ℓ))
            (c ℓ i a) ≤ L₀) →
          (∀ ℓ i, totalCurvature (productL2Metric I J (g a) (scaledFactorMetric h₀ ℓ))
            (c ℓ i a) ≤ Θ₀) →
          ∀ ℓ i, ∀ t ∈ Icc a b,
            curveLength (productL2Metric I J (g t) (scaledFactorMetric h₀ ℓ)) (c ℓ i t) ≤
              L₀ * Real.exp (B * (b - a)) ∧
            totalCurvature (productL2Metric I J (g t) (scaledFactorMetric h₀ ℓ)) (c ℓ i t) ≤
              (Θ₀ + L₀) * Real.exp (C * (b - a)) := by
  obtain ⟨B, C, hB, hC, hestimate⟩ :=
    exists_scaledFactor_curve_bounds (I := I) (J := J) (N := N) hg hab hdim
  refine ⟨B, C, hB, hC, ?_⟩
  intro h₀ ι c hc L₀ Θ₀ hL₀ hΘ₀ ℓ i t ht
  have h := hestimate h₀ ι c hc L₀ Θ₀ hL₀ hΘ₀ ℓ i t ht
  have hLa : 0 ≤ curveLength (productL2Metric I J (g a) (scaledFactorMetric h₀ ℓ))
      (c ℓ i a) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x _
    exact curveSpeed_nonneg _ _ _
  have hΘa : 0 ≤ totalCurvature (productL2Metric I J (g a) (scaledFactorMetric h₀ ℓ))
      (c ℓ i a) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x _
    exact mul_nonneg (curvature_nonneg _ _ _) (curveSpeed_nonneg _ _ _)
  have hLpos : 0 ≤ L₀ := hLa.trans (hL₀ ℓ i)
  have hΘpos : 0 ≤ Θ₀ := hΘa.trans (hΘ₀ ℓ i)
  have htime := sub_le_sub_right ht.2 a
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hB)) hLpos),
    h.2.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hC)) (add_nonneg hΘpos hLpos))⟩

#print axioms scaledFactorMetric
#print axioms scaledFactorMetric_inner
#print axioms scaledFactorMetric_norm
#print axioms scaledFactorMetric_static
#print axioms scaledProduct_isRicciFlow
#print axioms exists_scaledFactor_curve_bounds
#print axioms exists_scaledFactor_fullInterval_bounds
end CurveControl.Examples.StaticFactorApplication
