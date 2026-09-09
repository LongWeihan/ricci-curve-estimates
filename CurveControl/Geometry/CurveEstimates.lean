import CurveControl.Geometry.AmbientBounds
import CurveControl.Geometry.CurveRegularity
import CurveControl.Geometry.SpeedEvolution
import CurveControl.Geometry.CurvatureGradient
import CurveControl.Geometry.CurvatureEvolution
import CurveControl.Analysis.CurveEstimateAssembly

open Set Filter MeasureTheory Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff Interval
noncomputable section
namespace CurveControl.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The actual normal part of the arclength curvature gradient,
measured with the evolving metric. -/
def normalCurvatureGradientNorm (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (x : ℝ) : ℝ :=
  Real.sqrt (g.metricInner (γ x) (normalCurvatureGradient g γ x)
    (normalCurvatureGradient g γ x))

/-- **Math.** The actual ambient Ricci curvature in the unit tangent direction. -/
def tangentRicci (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) : ℝ :=
  ricciTensorAt g (γ x) (unitTangent g γ x) (unitTangent g γ x)

/-- **Math.** The corrected ambient contribution admits one coefficient
multiplying q plus square root q; that coefficient is independent of the curve. -/
theorem curve_ambient_error_le_max
    {g : Riemannian.RiemannianMetric I M} (γ : ℝ → M) (x : ℝ)
    {B K D : ℝ} (hBounds : AmbientBounds.TensorBoundsAt g (γ x) B K D)
    (himm : curveVelocity (I := I) γ x ≠ 0) :
    let S := unitTangent g γ x
    let V := curvatureVector g γ x
    ((4 * curvatureSq g γ x * ricciTensorAt g (γ x) S S -
        2 * ricciTensorAt g (γ x) V V + 2 * AmbientBounds.rm g (γ x) V S V S) +
      (-4 * AmbientBounds.covRic g (γ x) S S V + 2 * AmbientBounds.covRic g (γ x) V S S)) ≤
      max (6 * B + 2 * K) (6 * D) *
        (curvatureSq g γ x + Real.sqrt (curvatureSq g γ x)) := by
  dsimp only
  have h := (le_abs_self _).trans (AmbientBounds.curve_ambient_error γ x hBounds himm)
  have hq := mul_le_mul_of_nonneg_right (le_max_left (6 * B + 2 * K) (6 * D))
    (curvatureSq_nonneg g γ x)
  have hk := mul_le_mul_of_nonneg_right (le_max_right (6 * B + 2 * K) (6 * D))
    (curvature_nonneg g γ x)
  change _ ≤ max (6 * B + 2 * K) (6 * D) * (curvatureSq g γ x + curvature g γ x)
  nlinarith

namespace IsCurveShorteningFlowOn
variable {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
  (hc : IsCurveShorteningFlowOn (I := I) g c J) (hflow : IsRicciFlowOn g J)
include hc hflow

omit [SigmaCompactSpace M] [T2Space M] hflow in
/-- **Math.** Genuine Kato inequality from the actual smooth immersed flow.
The mixed-derivative theorem supplies the required covariant differentiability. -/
theorem curvatureSq_kato_closed {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    (Analysis.arcDeriv (curveSpeed (g t) (c t)) (curvatureSq (g t) (c t)) x) ^ 2 ≤
      4 * curvatureSq (g t) (c t) x * normalCurvatureGradientNorm (g t) (c t) x ^ 2 := by
  obtain ⟨D, _, hD⟩ := hc.exists_mixed_covDeriv ht x
  have hcov : HasCovDerivAlongAt (I := I) (g t) (c t) (curvatureVector (g t) (c t)) x
      (covDerivAlong (g t) (c t) (curvatureVector (g t) (c t)) x) := by
    rw [covDerivAlong_eq_of_hasCovDeriv (g t) (c t) (curvatureVector (g t) (c t)) x D hD]
    exact hD
  exact curvatureSq_kato_sqrt (g t) (c t) (hc.contMDiff_curve (interior_subset ht))
    (hc.immersed t (interior_subset ht)) x hcov

/-- **Math.** Assembly adapter: all scalar hypotheses except the squared-PDE
are derived here from the real flow. The final geometric theorem below supplies
that remaining PDE from the actual curvature evolution. -/
theorem scalarCurveHypotheses_of_squaredPDE {a b B K D : ℝ}
    (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hBounds : AmbientBounds.UniformTensorBoundsOn g J B K D)
    (hqPDE : ∀ t ∈ Ioo a b, ∀ x,
      deriv (fun u => curvatureSq (g u) (c u) x) t ≤
        Analysis.arcDeriv (curveSpeed (g t) (c t))
          (Analysis.arcDeriv (curveSpeed (g t) (c t)) (curvatureSq (g t) (c t))) x -
        2 * normalCurvatureGradientNorm (g t) (c t) x ^ 2 +
        2 * curvatureSq (g t) (c t) x ^ 2 +
        max (6 * B + 2 * K) (6 * D) *
          (curvatureSq (g t) (c t) x + Real.sqrt (curvatureSq (g t) (c t) x))) :
    Analysis.ScalarCurveHypotheses
      (fun t x => curvatureSq (g t) (c t) x)
      (fun t x => curveSpeed (g t) (c t) x)
      (fun t x => tangentRicci (g t) (c t) x)
      (fun t x => normalCurvatureGradientNorm (g t) (c t) x)
      a b (max (6 * B + 2 * K) (6 * D)) B := by
  have hJi : Ioo a b ⊆ interior J := by
    intro t ht
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hJ)
  have hB0 := hBounds a (hJ ⟨le_rfl, hab⟩) (c a 0)
  constructor
  · intro p hp
    exact (hc.contDiffAt_curvatureSq hflow.smooth (hJi hp.1)).contDiffWithinAt
  · intro p hp
    exact (hc.contDiffAt_curveSpeed hflow.smooth (hJi hp.1)).contDiffWithinAt
  · exact hc.continuousOn_curvatureSq_rectangle hflow.smooth (uniqueDiffOn_ricciTime hflow) hJ
  · exact hc.continuousOn_curveSpeed_rectangle hflow.smooth (uniqueDiffOn_ricciTime hflow) hJ
  · exact fun t _ x => curvatureSq_nonneg (g t) (c t) x
  · exact fun t ht x => hc.speed_pos (hJ ht) x
  · exact fun t ht => curvatureSq_periodic (g t) (c t) (hc.closed t (hJ (Ioo_subset_Icc_self ht)))
  · exact fun t ht => curveSpeed_periodic (g t) (c t) (hc.closed t (hJ (Ioo_subset_Icc_self ht)))
  · exact le_max_of_le_left (by linarith [hB0.ricci_nonneg, hB0.curvature_nonneg])
  · exact hB0.ricci_nonneg
  · intro t ht x
    exact (hBounds t (hJ (Ioo_subset_Icc_self ht)) (c t x)).ricci_unit
      (hc.tangent_unit (hJ (Ioo_subset_Icc_self ht)) x)
  · exact fun t ht x => (hc.hasDerivAt_curveSpeed_time hflow (hJi ht) x).deriv
  · exact fun t ht x => hc.curvatureSq_kato_closed (hJi ht) x
  · exact hqPDE

/-- **Math.** The actual squared-curvature PDE with a uniform ambient
coefficient. Its evolution, normal-gradient dissipation, and tensor error all
come from proved geometric identities. -/
theorem curvatureSq_time_le {B K D : ℝ}
    (hBounds : AmbientBounds.UniformTensorBoundsOn g J B K D)
    {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    deriv (fun u => curvatureSq (g u) (c u) x) t ≤
      Analysis.arcDeriv (curveSpeed (g t) (c t))
        (Analysis.arcDeriv (curveSpeed (g t) (c t)) (curvatureSq (g t) (c t))) x -
      2 * normalCurvatureGradientNorm (g t) (c t) x ^ 2 +
      2 * curvatureSq (g t) (c t) x ^ 2 +
      max (6 * B + 2 * K) (6 * D) *
        (curvatureSq (g t) (c t) x + Real.sqrt (curvatureSq (g t) (c t) x)) := by
  have hq := (hc.hasDerivAt_curvatureSq_time hflow ht x).deriv
  have herr := curve_ambient_error_le_max (c t) x
    (hBounds t (interior_subset ht) (c t x)) (hc.immersed t (interior_subset ht) x)
  dsimp only at hq herr
  rw [hq]
  dsimp only [normalCurvatureGradientNorm]
  rw [Real.sq_sqrt ((g t).metricInner_self_nonneg _ _)]
  linarith

/-- **Math.** The complete actual length and total-curvature estimate. The
same ambient constants work for every immersed closed curve-shortening flow.
Only smooth existence, the Ricci/curve-flow equations and ambient tensor bounds
are inputs; there are no curvature-PDE, Kato, regularization or integral inputs. -/
theorem curve_estimate {a b B K D : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hBounds : AmbientBounds.UniformTensorBoundsOn g J B K D) :
    ∀ t ∈ Icc a b,
      curveLength (g t) (c t) ≤ curveLength (g a) (c a) * Real.exp (B * (t - a)) ∧
      totalCurvature (g t) (c t) + curveLength (g t) (c t) ≤
        (totalCurvature (g a) (c a) + curveLength (g a) (c a)) *
          Real.exp ((max (6 * B + 2 * K) (6 * D) / 2 + B) * (t - a)) := by
  have hJi : Ioo a b ⊆ interior J := by
    intro t ht
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hJ)
  have hs := hc.scalarCurveHypotheses_of_squaredPDE hflow hab hJ hBounds
    (fun t ht x => hc.curvatureSq_time_le hflow hBounds (hJi ht) x)
  simpa only [CurveControl.weightedCurvature, totalCurvature, curveLength, curvature] using
    hs.curve_estimate

end IsCurveShorteningFlowOn
/-- **Math.** The same ambient coefficients control an arbitrary family of
actual curve-shortening flows; no regularity in the family index is needed. -/
theorem curve_family_estimate {ι : Type*}
    {g : ℝ → Riemannian.RiemannianMetric I M} {c : ι → ℝ → ℝ → M} {J : Set ℝ}
    (hc : ∀ i, IsCurveShorteningFlowOn (I := I) g (c i) J) (hflow : IsRicciFlowOn g J)
    {a b B K D : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hBounds : AmbientBounds.UniformTensorBoundsOn g J B K D) :
    ∀ i, ∀ t ∈ Icc a b,
      curveLength (g t) (c i t) ≤ curveLength (g a) (c i a) * Real.exp (B * (t - a)) ∧
      totalCurvature (g t) (c i t) + curveLength (g t) (c i t) ≤
        (totalCurvature (g a) (c i a) + curveLength (g a) (c i a)) *
          Real.exp ((max (6 * B + 2 * K) (6 * D) / 2 + B) * (t - a)) :=
  fun i => (hc i).curve_estimate hflow hab hJ hBounds

/-- **Math.** Uniform initial length and total-curvature bounds propagate
uniformly across the family with coefficients depending only on the ambient
metric bounds. -/
theorem curve_family_uniform_estimate {ι : Type*}
    {g : ℝ → Riemannian.RiemannianMetric I M} {c : ι → ℝ → ℝ → M} {J : Set ℝ}
    (hc : ∀ i, IsCurveShorteningFlowOn (I := I) g (c i) J) (hflow : IsRicciFlowOn g J)
    {a b B K D L₀ Q₀ : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hBounds : AmbientBounds.UniformTensorBoundsOn g J B K D)
    (hL₀ : ∀ i, curveLength (g a) (c i a) ≤ L₀)
    (hQ₀ : ∀ i, totalCurvature (g a) (c i a) + curveLength (g a) (c i a) ≤ Q₀) :
    ∀ i, ∀ t ∈ Icc a b,
      curveLength (g t) (c i t) ≤ L₀ * Real.exp (B * (t - a)) ∧
      totalCurvature (g t) (c i t) + curveLength (g t) (c i t) ≤
        Q₀ * Real.exp ((max (6 * B + 2 * K) (6 * D) / 2 + B) * (t - a)) := by
  intro i t ht
  have h := (hc i).curve_estimate hflow hab hJ hBounds t ht
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right (hL₀ i) (Real.exp_pos _).le),
    h.2.trans (mul_le_mul_of_nonneg_right (hQ₀ i) (Real.exp_pos _).le)⟩

#print axioms curve_ambient_error_le_max
#print axioms IsCurveShorteningFlowOn.curvatureSq_kato_closed
#print axioms IsCurveShorteningFlowOn.scalarCurveHypotheses_of_squaredPDE
#print axioms IsCurveShorteningFlowOn.curvatureSq_time_le
#print axioms IsCurveShorteningFlowOn.curve_estimate
#print axioms curve_family_estimate
#print axioms curve_family_uniform_estimate
end CurveControl.Geometry
