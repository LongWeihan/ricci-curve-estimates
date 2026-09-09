import CurveControl.Geometry.CurveEstimates
import CurveControl.Geometry.ProductFlow
import CurveControl.Geometry.ProductAmbientBounds
import CurveControl.Geometry.ProductCovRicci
import CurveControl.Geometry.CompactAmbientBounds

/-!
# Uniform estimates for curves in genuine products with static 1D factors

The factor is an actual smooth one-dimensional Riemannian manifold. Its metric
may vary arbitrarily with an external index but is static in Ricci-flow time.
This formulation includes a supplied smooth circle and its scaled metrics;
it does not construct an AddCircle atlas.
-/
open Set Filter MeasureTheory Riemannian MorganTianLib
open scoped Manifold Topology ContDiff Interval
noncomputable section
namespace CurveControl.Geometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]

/-- **Math.** Covariant Ricci of an actual static one-dimensional factor is
zero, since the actual Ricci field vanishes identically before differentiation. -/
theorem ambientCovRic_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ F = 1) (h : Riemannian.RiemannianMetric J N)
    (p : N) (u v w : TangentSpace J p) : AmbientBounds.covRic h p u v w = 0 := by
  unfold AmbientBounds.covRic
  exact covRicciAt_eq_zero_of_finrank_one hdim h h.leviCivitaConnection _ p u v w

/-- **Math.** Norm comparison for the covariant-Ricci product identity.
The identity argument is supplied by the independent genuine product-tensor
splitting theorem in the closed wrapper below. -/
theorem productL2_covRic_bound_of_split
    (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) {B R D : ℝ} (hb : AmbientBounds.TensorBoundsAt g p.1 B R D)
    (hdim : Module.finrank ℝ F = 1)
    (hSplit : ∀ u v w : TangentSpace (productL2Model I J) p,
      AmbientBounds.covRic (productL2Metric I J g h) p u v w =
        AmbientBounds.covRic g p.1 (productL2Equiv.symm u).1
          (productL2Equiv.symm v).1 (productL2Equiv.symm w).1 +
        AmbientBounds.covRic h p.2 (productL2Equiv.symm u).2
          (productL2Equiv.symm v).2 (productL2Equiv.symm w).2)
    (u v w : TangentSpace (productL2Model I J) p) :
    |AmbientBounds.covRic (productL2Metric I J g h) p u v w| ≤
      D * AmbientBounds.metricNorm (productL2Metric I J g h) p u *
        AmbientBounds.metricNorm (productL2Metric I J g h) p v *
        AmbientBounds.metricNorm (productL2Metric I J g h) p w := by
  rw [hSplit, ambientCovRic_eq_zero_of_finrank_one J hdim h, add_zero]
  calc
    _ ≤ D * AmbientBounds.metricNorm g p.1 (productL2Equiv.symm u).1 *
        AmbientBounds.metricNorm g p.1 (productL2Equiv.symm v).1 *
        AmbientBounds.metricNorm g p.1 (productL2Equiv.symm w).1 := hb.covRic _ _ _
    _ ≤ _ := by
      have hD := hb.covRic_nonneg
      gcongr <;> first
      | exact productL2_metricNorm_fst_le g h p _
      | (unfold AmbientBounds.metricNorm; positivity)

/-- **Math.** Full pointwise product bounds preserve all three base constants
once the actual covariant-Ricci splitting is supplied. -/
theorem productL2_tensorBounds_of_covRic_split
    (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) {B R D : ℝ} (hb : AmbientBounds.TensorBoundsAt g p.1 B R D)
    (hdim : Module.finrank ℝ F = 1)
    (hSplit : ∀ u v w : TangentSpace (productL2Model I J) p,
      AmbientBounds.covRic (productL2Metric I J g h) p u v w =
        AmbientBounds.covRic g p.1 (productL2Equiv.symm u).1
          (productL2Equiv.symm v).1 (productL2Equiv.symm w).1 +
        AmbientBounds.covRic h p.2 (productL2Equiv.symm u).2
          (productL2Equiv.symm v).2 (productL2Equiv.symm w).2) :
    AmbientBounds.TensorBoundsAt (productL2Metric I J g h) p B R D := by
  exact ⟨hb.ricci_nonneg, hb.curvature_nonneg, hb.covRic_nonneg,
    productL2_ricci_bound_of_finrank_one g h p hb hdim,
    productL2_curvature_bound_of_finrank_one g h p hb hdim,
    productL2_covRic_bound_of_split I J g h p hb hdim hSplit⟩

/-- **Math.** All ambient tensor bounds of a genuine product with any static
one-dimensional metric are inherited from the base with unchanged constants.
The product curvature and covariant-Ricci splittings are proved, not assumed. -/
theorem productL2_tensorBounds_of_finrank_one
    (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) {B R D : ℝ} (hb : AmbientBounds.TensorBoundsAt g p.1 B R D)
    (hdim : Module.finrank ℝ F = 1) :
    AmbientBounds.TensorBoundsAt (productL2Metric I J g h) p B R D :=
  productL2_tensorBounds_of_covRic_split I J g h p hb hdim
    (ProductCovRicci.covRic_productL2 g h p)

/-- **Math.** The same three constants control the product over the entire
base time set, independently of the chosen static one-dimensional metric. -/
theorem uniformTensorBoundsOn_productL2_oneDimensional
    {g : ℝ → Riemannian.RiemannianMetric I M} {T : Set ℝ} {B R D : ℝ}
    (hb : AmbientBounds.UniformTensorBoundsOn g T B R D)
    (h : Riemannian.RiemannianMetric J N) (hdim : Module.finrank ℝ F = 1) :
    AmbientBounds.UniformTensorBoundsOn (fun t => productL2Metric I J (g t) h) T B R D :=
  fun t ht p => productL2_tensorBounds_of_finrank_one I J (g t) h p (hb t ht p.1) hdim

/-- **Math.** Product-family estimates from uniform actual product tensors.
Ricci-flow status of every product is proved from the base flow and the static
one-dimensional factor, rather than supplied as a hypothesis. -/
theorem static_product_family_estimate_of_tensorBounds {Λ ι : Type*}
    {g : ℝ → Riemannian.RiemannianMetric I M} {a b B R D L₀ Θ₀ : ℝ}
    (hg : IsRicciFlowOn g (Icc a b)) (hab : a ≤ b) (hdim : Module.finrank ℝ F = 1)
    (h : Λ → Riemannian.RiemannianMetric J N) (c : Λ → ι → ℝ → ℝ → M × N)
    (hc : ∀ ℓ i, IsCurveShorteningFlowOn (I := productL2Model I J)
      (fun t => productL2Metric I J (g t) (h ℓ)) (c ℓ i) (Icc a b))
    (hBounds : ∀ ℓ, AmbientBounds.UniformTensorBoundsOn
      (fun t => productL2Metric I J (g t) (h ℓ)) (Icc a b) B R D)
    (hL₀ : ∀ ℓ i, curveLength (productL2Metric I J (g a) (h ℓ)) (c ℓ i a) ≤ L₀)
    (hΘ₀ : ∀ ℓ i, totalCurvature (productL2Metric I J (g a) (h ℓ)) (c ℓ i a) ≤ Θ₀) :
    ∀ ℓ i, ∀ t ∈ Icc a b,
      curveLength (productL2Metric I J (g t) (h ℓ)) (c ℓ i t) ≤
        L₀ * Real.exp (B * (t - a)) ∧
      totalCurvature (productL2Metric I J (g t) (h ℓ)) (c ℓ i t) ≤
        (Θ₀ + L₀) * Real.exp ((max (6 * B + 2 * R) (6 * D) / 2 + B) * (t - a)) := by
  intro ℓ i t ht
  have hp := isRicciFlowOn_productL2_oneDimensional I J hg (h ℓ) hdim
  have hresult := curve_family_uniform_estimate (hc ℓ) hp hab (Subset.refl _)
    (hBounds ℓ) (hL₀ ℓ) (fun i => add_le_add (hΘ₀ ℓ i) (hL₀ ℓ i)) i t ht
  have hLnonneg : 0 ≤ curveLength (productL2Metric I J (g t) (h ℓ)) (c ℓ i t) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x _
    exact curveSpeed_nonneg _ _ _
  exact ⟨hresult.1, (le_add_of_nonneg_right hLnonneg).trans hresult.2⟩

/-- **Math.** Compactness of the base metric family alone supplies the three
finite ambient coefficients used by all static-factor estimates. No factor
metric, curve family or initial length enters this existence statement. -/
theorem compact_base_uniform_coefficients [CompactSpace M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {a b : ℝ}
    (hg : IsRicciFlowOn g (Icc a b)) :
    ∃ B R D : ℝ, 0 ≤ B ∧ 0 ≤ R ∧ 0 ≤ D ∧
      AmbientBounds.UniformTensorBoundsOn g (Icc a b) B R D :=
  CompactAmbientBounds.exists_uniformTensorBoundsOn hg.smooth (Subset.refl _)

/-- **Math.** Compact-base uniform product estimate. The constants are chosen
before the arbitrary external metric index, all static factor metrics, all
curve indices and the initial bounds. Thus neither shrinking/scaling the
factor metric nor selecting another curve changes the exponential constants.
The one-dimensional factor is genuine supplied manifold geometry, not an
assumed circle atlas. -/
theorem exists_uniform_static_product_family_estimate [CompactSpace M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {a b : ℝ}
    (hg : IsRicciFlowOn g (Icc a b)) (hab : a ≤ b) (hdim : Module.finrank ℝ F = 1) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (Λ ι : Type*) (h : Λ → Riemannian.RiemannianMetric J N)
        (c : Λ → ι → ℝ → ℝ → M × N),
        (∀ ℓ i, IsCurveShorteningFlowOn (I := productL2Model I J)
          (fun t => productL2Metric I J (g t) (h ℓ)) (c ℓ i) (Icc a b)) →
        ∀ L₀ Θ₀ : ℝ,
          (∀ ℓ i, curveLength (productL2Metric I J (g a) (h ℓ)) (c ℓ i a) ≤ L₀) →
          (∀ ℓ i, totalCurvature (productL2Metric I J (g a) (h ℓ)) (c ℓ i a) ≤ Θ₀) →
          ∀ ℓ i, ∀ t ∈ Icc a b,
            curveLength (productL2Metric I J (g t) (h ℓ)) (c ℓ i t) ≤
              L₀ * Real.exp (B * (t - a)) ∧
            totalCurvature (productL2Metric I J (g t) (h ℓ)) (c ℓ i t) ≤
              (Θ₀ + L₀) * Real.exp (C * (t - a)) := by
  obtain ⟨B, R, D, hB, hR, hD, hBounds⟩ := compact_base_uniform_coefficients I hg
  have hA : 0 ≤ max (6 * B + 2 * R) (6 * D) :=
    le_max_of_le_left (by linarith)
  refine ⟨B, max (6 * B + 2 * R) (6 * D) / 2 + B, hB, by positivity, ?_⟩
  intro Λ ι h c hc L₀ Θ₀ hL₀ hΘ₀
  exact static_product_family_estimate_of_tensorBounds I J hg hab hdim h c hc
    (fun ℓ => uniformTensorBoundsOn_productL2_oneDimensional I J hBounds (h ℓ) hdim)
    hL₀ hΘ₀

/-- **Math.** Positive-scale-indexed corollary. The supplied metrics may, for
example, be scaled metrics on an independently supplied smooth circle. No
lower bound on the scale, nor any scale-regularity hypothesis, is required.
All exponential coefficients are chosen before the entire metric family. -/
theorem exists_uniform_positive_scale_product_estimate [CompactSpace M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {a b : ℝ}
    (hg : IsRicciFlowOn g (Icc a b)) (hab : a ≤ b) (hdim : Module.finrank ℝ F = 1) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (ι : Type*) (h : {ℓ : ℝ // 0 < ℓ} → Riemannian.RiemannianMetric J N)
        (c : {ℓ : ℝ // 0 < ℓ} → ι → ℝ → ℝ → M × N),
        (∀ ℓ i, IsCurveShorteningFlowOn (I := productL2Model I J)
          (fun t => productL2Metric I J (g t) (h ℓ)) (c ℓ i) (Icc a b)) →
        ∀ L₀ Θ₀ : ℝ,
          (∀ ℓ i, curveLength (productL2Metric I J (g a) (h ℓ)) (c ℓ i a) ≤ L₀) →
          (∀ ℓ i, totalCurvature (productL2Metric I J (g a) (h ℓ)) (c ℓ i a) ≤ Θ₀) →
          ∀ ℓ i, ∀ t ∈ Icc a b,
            curveLength (productL2Metric I J (g t) (h ℓ)) (c ℓ i t) ≤
              L₀ * Real.exp (B * (t - a)) ∧
            totalCurvature (productL2Metric I J (g t) (h ℓ)) (c ℓ i t) ≤
              (Θ₀ + L₀) * Real.exp (C * (t - a)) := by
  obtain ⟨B, C, hB, hC, hresult⟩ :=
    exists_uniform_static_product_family_estimate I J (N := N) hg hab hdim
  exact ⟨B, C, hB, hC, fun ι h c hc L₀ Θ₀ hL₀ hΘ₀ =>
    hresult {ℓ : ℝ // 0 < ℓ} ι h c hc L₀ Θ₀ hL₀ hΘ₀⟩

#print axioms ambientCovRic_eq_zero_of_finrank_one
#print axioms productL2_covRic_bound_of_split
#print axioms productL2_tensorBounds_of_covRic_split
#print axioms static_product_family_estimate_of_tensorBounds
#print axioms compact_base_uniform_coefficients
#print axioms productL2_tensorBounds_of_finrank_one
#print axioms uniformTensorBoundsOn_productL2_oneDimensional
#print axioms exists_uniform_static_product_family_estimate
#print axioms exists_uniform_positive_scale_product_estimate
end CurveControl.Geometry
