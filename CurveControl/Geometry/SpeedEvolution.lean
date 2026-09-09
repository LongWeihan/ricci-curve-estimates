import CurveControl.Geometry.ChartBridge
import CurveControl.Geometry.SpatialCurve
import CurveControl.Geometry.MovingMetric
import MorganTianLib.Ch02.CovDerivAlongMap

open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff
noncomputable section
namespace CurveControl.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Recover velocity by multiplying the unit tangent by speed. -/
theorem curveVelocity_eq_speed_smul_unitTangent
    (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M) {x : ℝ}
    (himm : curveVelocity (I := I) γ x ≠ 0) :
    curveVelocity (I := I) γ x = curveSpeed g γ x • unitTangent g γ x := by
  rw [unitTangent, smul_smul, mul_inv_cancel₀ (ne_of_gt (curveSpeed_pos g γ x himm)), one_smul]

/-- **Math.** Parameter derivative of the unit tangent is speed times curvature. -/
theorem covDeriv_unitTangent_eq_speed_smul_curvature
    (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M) {x : ℝ}
    (himm : curveVelocity (I := I) γ x ≠ 0) :
    covDerivAlong g γ (unitTangent g γ) x =
      curveSpeed g γ x • curvatureVector g γ x := by
  rw [curvatureVector, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (curveSpeed_pos g γ x himm)), one_smul]

/-- **Math.** Differentiate the proved orthogonality of curvature and tangent.
The resulting contraction is the negative squared-curvature speed term. -/
theorem metricInner_covDeriv_curvature_velocity
    (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) {x : ℝ} {D : E}
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x D) :
    g.metricInner (γ x) D (curveVelocity (I := I) γ x) =
      -(curveSpeed g γ x ^ 2 * curvatureSq g γ x) := by
  have hS := hasCovDerivAlongAt_unitTangent g γ hγ x (himm x)
  have hp := hD.hasDerivAt_metricInner hS
  have heq : (fun y => g.metricInner (γ y) (curvatureVector g γ y)
      (unitTangent g γ y)) = fun _ => (0 : ℝ) := by
    funext y
    exact curvatureVector_orthogonal_of_contMDiff g γ hγ himm y
  rw [heq] at hp
  have hzero := hp.unique (hasDerivAt_const x (0 : ℝ))
  rw [covDeriv_unitTangent_eq_speed_smul_curvature g γ (himm x),
    g.metricInner_smul_right] at hzero
  rw [curveVelocity_eq_speed_smul_unitTangent g γ (himm x), g.metricInner_smul_right]
  change curveSpeed g γ x * g.metricInner (γ x) D (unitTangent g γ x) = _
  change g.metricInner (γ x) D (unitTangent g γ x) +
    curveSpeed g γ x * curvatureSq g γ x = 0 at hzero
  rw [show g.metricInner (γ x) D (unitTangent g γ x) =
    -(curveSpeed g γ x * curvatureSq g γ x) by linarith]
  ring

/-- **Math.** The geometric speed formula once the two actual mixed covariant
derivatives are identified. The closed flow theorem below supplies this
identification by the upstream fixed-chart Schwarz and torsion-free theorem. -/
theorem hasDerivAt_time_curveSpeed_of_mixed [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t x : ℝ} (ht : t ∈ interior J)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ (c t))
    (himm : ∀ y, curveVelocity (I := I) (c t) y ≠ 0) {D : E}
    (hDt : HasCovDerivAlongAt (I := I) (g t) (fun s => c s x)
      (fun s => curveVelocity (I := I) (c s) x) t D)
    (hDx : HasCovDerivAlongAt (I := I) (g t) (c t)
      (curvatureVector (g t) (c t)) x D) :
    HasDerivAt (fun s => curveSpeed (g s) (c s) x)
      (-(curvatureSq (g t) (c t) x + ricciTensorAt (g t) (c t x)
        (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x)) *
        curveSpeed (g t) (c t) x) t := by
  have hpair := metricInner_covDeriv_curvature_velocity (g t) (c t) hc himm hDx
  have hsquare := hasDerivAt_ricciFlow_field_sq hflow ht hDt
  have hsqrt := hsquare.sqrt
    (ne_of_gt ((g t).metricInner_self_pos _ _ (himm x)))
  have hv : curveSpeed (g t) (c t) x ≠ 0 :=
    ne_of_gt (curveSpeed_pos (g t) (c t) x (himm x))
  have hric : ricciTensorAt (g t) (c t x)
      (curveVelocity (I := I) (c t) x) (curveVelocity (I := I) (c t) x) =
      curveSpeed (g t) (c t) x ^ 2 * ricciTensorAt (g t) (c t x)
        (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x) := by
    rw [curveVelocity_eq_speed_smul_unitTangent (g t) (c t) (himm x)]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  apply hsqrt.congr_deriv
  change (-2 * ricciTensorAt (g t) (c t x)
      (curveVelocity (I := I) (c t) x) (curveVelocity (I := I) (c t) x) +
      2 * (g t).metricInner (c t x) D (curveVelocity (I := I) (c t) x)) /
      (2 * curveSpeed (g t) (c t) x) = _
  rw [hpair, hric]
  field_simp
  ring

/-- **Math.** Actual mixed covariant derivatives agree: the time derivative
of spatial velocity equals the spatial derivative of curvature. Smoothness,
Schwarz symmetry, torsion freedom and the defining flow PDE prove the equality. -/
theorem IsCurveShorteningFlowOn.exists_mixed_covDeriv
    {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : IsCurveShorteningFlowOn (I := I) g c J)
    {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    ∃ D : E,
      HasCovDerivAlongAt (I := I) (g t) (fun s => c s x)
        (fun s => curveVelocity (I := I) (c s) x) t D ∧
      HasCovDerivAlongAt (I := I) (g t) (c t)
        (curvatureVector (g t) (c t)) x D := by
  have hcont : ContinuousAt (fun p : ℝ × ℝ => c p.1 p.2) (t, x) :=
    (hc.contMDiffAt_family ht).continuousAt
  have hu : ContDiffAt ℝ 2
      (chartLocalMap (I := I) (fun p : ℝ × ℝ => c p.1 p.2) t x) (t, x) :=
    contDiffAt_infty.mp (hc.contDiffAt_chartCurveFamily (c t x) (p := (t, x)) ht
      (mem_chart_source H (c t x))) 2
  obtain ⟨D, hDt, hDx⟩ := hasCovDerivAlongAt_fst_snd_symm (I := I) hcont hu (g t)
  have heq : (fun y => curveVelocity (I := I) (fun s => c s y) t) =
      curvatureVector (g t) (c t) := by
    funext y
    exact hc.timeVelocity_eq_curvatureVector ht y
  change HasCovDerivAlongAt (I := I) (g t) (c t)
    (fun y => curveVelocity (I := I) (fun s => c s y) t) x D at hDx
  rw [heq] at hDx
  exact ⟨D, hDt, hDx⟩

/-- **Math.** Arc-length density evolution for an actual smooth immersed
curve-shortening flow in an actual Ricci flow. Mixed covariant derivatives are
proved equal through a fixed local chart; no speed evolution is an input. -/
theorem IsCurveShorteningFlowOn.hasDerivAt_curveSpeed_time
    [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : IsCurveShorteningFlowOn (I := I) g c J) (hflow : IsRicciFlowOn g J)
    {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasDerivAt (fun s => curveSpeed (g s) (c s) x)
      (-(curvatureSq (g t) (c t) x + ricciTensorAt (g t) (c t x)
        (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x)) *
        curveSpeed (g t) (c t) x) t := by
  obtain ⟨D, hDt, hDx⟩ := hc.exists_mixed_covDeriv ht x
  exact hasDerivAt_time_curveSpeed_of_mixed hflow ht
    (hc.contMDiff_curve (interior_subset ht))
    (hc.immersed t (interior_subset ht)) hDt hDx

/-- **Math.** Actual unit-tangent time evolution under curve shortening and
Ricci flow, obtained by differentiating speed inverse times spatial velocity. -/
theorem IsCurveShorteningFlowOn.hasCovDerivAt_unitTangent_time
    [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : IsCurveShorteningFlowOn (I := I) g c J) (hflow : IsRicciFlowOn g J)
    {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasCovDerivAlongAt (I := I) (g t) (fun s => c s x)
      (fun s => unitTangent (g s) (c s) x) t
      ((curveSpeed (g t) (c t) x)⁻¹ •
          covDerivAlong (g t) (c t) (curvatureVector (g t) (c t)) x +
        (curvatureSq (g t) (c t) x + ricciTensorAt (g t) (c t x)
          (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x)) •
          unitTangent (g t) (c t) x) := by
  obtain ⟨D, hDt, hDx⟩ := hc.exists_mixed_covDeriv ht x
  let a := curvatureSq (g t) (c t) x + ricciTensorAt (g t) (c t x)
    (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x)
  have hv : curveSpeed (g t) (c t) x ≠ 0 := ne_of_gt (hc.speed_pos (interior_subset ht) x)
  have hinv : HasDerivAt (fun s => (curveSpeed (g s) (c s) x)⁻¹)
      (a * (curveSpeed (g t) (c t) x)⁻¹) t := by
    apply ((hc.hasDerivAt_curveSpeed_time hflow ht x).inv hv).congr_deriv
    change -(-a * curveSpeed (g t) (c t) x) / curveSpeed (g t) (c t) x ^ 2 = _
    field_simp
  have hS := HasCovDerivAlongAt.smul_fun hinv hDt
  rw [chartFieldCoord_self (I := I) (fun s => c s x)
    (fun s => curveVelocity (I := I) (c s) x) t] at hS
  have hscale : (a * (curveSpeed (g t) (c t) x)⁻¹) •
      curveVelocity (I := I) (c t) x = a • unitTangent (g t) (c t) x := by
    rw [curveVelocity_eq_speed_smul_unitTangent (g t) (c t)
      (hc.immersed t (interior_subset ht) x), smul_smul]
    congr 1
    field_simp
  convert hS using 1
  · rfl
  · rw [covDerivAlong_eq_of_hasCovDeriv (g t) (c t)
      (curvatureVector (g t) (c t)) x D hDx]
    let DT : TangentSpace I (c t x) := D
    exact (add_comm _ _).trans (congrArg (fun w : TangentSpace I (c t x) =>
      w + (curveSpeed (g t) (c t) x)⁻¹ • DT) hscale).symm

#print axioms metricInner_covDeriv_curvature_velocity
#print axioms hasDerivAt_time_curveSpeed_of_mixed
#print axioms IsCurveShorteningFlowOn.exists_mixed_covDeriv
#print axioms IsCurveShorteningFlowOn.hasDerivAt_curveSpeed_time
#print axioms IsCurveShorteningFlowOn.hasCovDerivAt_unitTangent_time
end CurveControl.Geometry
