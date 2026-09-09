import CurveControl.Geometry.SpatialCurve
import CurveControl.Analysis.WeightedIntegral
import Mathlib.Tactic.FieldSimp

/-!
# Spatial curvature gradient identities

All quantities use the actual moving-foot covariant derivative and metric.
The covariant differentiability predicates below concern genuine chart
derivatives. The Kato inequality and normal decomposition are conclusions.
-/

open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff

noncomputable section

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

def covArcDeriv (g : RiemannianMetric I M) (γ : ℝ → M)
    (W : ∀ x, TangentSpace I (γ x)) (x : ℝ) : TangentSpace I (γ x) :=
  (curveSpeed g γ x)⁻¹ • covDerivAlong g γ W x

def normalCurvatureGradient (g : RiemannianMetric I M) (γ : ℝ → M)
    (x : ℝ) : TangentSpace I (γ x) :=
  covArcDeriv g γ (curvatureVector g γ) x + curvatureSq g γ x • unitTangent g γ x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Cauchy--Schwarz for the actual metric, obtained from its positivity. -/
theorem metricInner_sq_le (g : RiemannianMetric I M) (p : M)
    (V W : TangentSpace I p) :
    (g.metricInner p V W) ^ 2 ≤ g.metricInner p V V * g.metricInner p W W := by
  by_cases hV : V = 0
  · simp [hV]
  have hpos := g.metricInner_self_pos p V hV
  have hn := g.metricInner_self_nonneg p
    (W - (g.metricInner p V W / g.metricInner p V V) • V)
  simp only [g.metricInner_sub_left, g.metricInner_sub_right,
    g.metricInner_smul_left, g.metricInner_smul_right,
    g.metricInner_comm p W V] at hn
  have heq : g.metricInner p V V *
      (g.metricInner p W W - (g.metricInner p V W / g.metricInner p V V) * g.metricInner p V W -
        (g.metricInner p V W / g.metricInner p V V) *
          (g.metricInner p V W - (g.metricInner p V W / g.metricInner p V V) * g.metricInner p V V)) =
      g.metricInner p V V * g.metricInner p W W - (g.metricInner p V W) ^ 2 := by
    field_simp
    ring
  have hm := mul_nonneg (le_of_lt hpos) hn
  have hh : 0 ≤ g.metricInner p V V * g.metricInner p W W - (g.metricInner p V W) ^ 2 := by
    rw [← heq]
    nlinarith only [hm]
  linarith

theorem hasDerivAt_curvatureSq (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ)
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x
      (covDerivAlong g γ (curvatureVector g γ) x)) :
    HasDerivAt (curvatureSq g γ)
      (2 * g.metricInner (γ x) (covDerivAlong g γ (curvatureVector g γ) x)
        (curvatureVector g γ x)) x := by
  have hh := hD.hasDerivAt_metricInner hD
  rw [g.metricInner_comm (γ x) (curvatureVector g γ x)
    (covDerivAlong g γ (curvatureVector g γ) x)] at hh
  change HasDerivAt (fun y => g.metricInner (γ y) (curvatureVector g γ y)
    (curvatureVector g γ y)) _ x
  simpa only [two_mul] using hh

theorem arcDeriv_curvatureSq (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ)
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x
      (covDerivAlong g γ (curvatureVector g γ) x)) :
    Analysis.arcDeriv (curveSpeed g γ) (curvatureSq g γ) x =
      2 * g.metricInner (γ x) (covArcDeriv g γ (curvatureVector g γ) x)
        (curvatureVector g γ x) := by
  unfold Analysis.arcDeriv covArcDeriv
  rw [(hasDerivAt_curvatureSq g γ x hD).deriv, g.metricInner_smul_left]
  ring

theorem normalCurvatureGradient_inner_curvature (g : RiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) (x : ℝ) :
    g.metricInner (γ x) (normalCurvatureGradient g γ x) (curvatureVector g γ x) =
      g.metricInner (γ x) (covArcDeriv g γ (curvatureVector g γ) x)
        (curvatureVector g γ x) := by
  unfold normalCurvatureGradient
  rw [g.metricInner_add_left, g.metricInner_smul_left,
    g.metricInner_comm (γ x) (unitTangent g γ x) (curvatureVector g γ x),
    curvatureVector_orthogonal_of_contMDiff g γ hγ himm x, mul_zero, add_zero]

/-- **Math.** Kato bound with the actual normal component of the curvature gradient.
There is no scalar gradient inequality among the hypotheses. -/
theorem curvatureSq_kato (g : RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) (x : ℝ)
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x
      (covDerivAlong g γ (curvatureVector g γ) x)) :
    (Analysis.arcDeriv (curveSpeed g γ) (curvatureSq g γ) x) ^ 2 ≤
      4 * curvatureSq g γ x *
        g.metricInner (γ x) (normalCurvatureGradient g γ x) (normalCurvatureGradient g γ x) := by
  rw [arcDeriv_curvatureSq g γ x hD,
    ← normalCurvatureGradient_inner_curvature g γ hγ himm x]
  have hh := metricInner_sq_le g (γ x) (normalCurvatureGradient g γ x) (curvatureVector g γ x)
  change _ ≤ 4 * g.metricInner (γ x) (curvatureVector g γ x) (curvatureVector g γ x) * _
  nlinarith

/-- **Math.** Differentiating the proved identity `g(H,S)=0` yields `g(DsH,S)=-q`. -/
theorem covArcDeriv_curvature_inner_tangent (g : RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) (x : ℝ)
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x
      (covDerivAlong g γ (curvatureVector g γ) x)) :
    g.metricInner (γ x) (covArcDeriv g γ (curvatureVector g γ) x) (unitTangent g γ x) =
      -curvatureSq g γ x := by
  have hprod := hD.hasDerivAt_metricInner
    (hasCovDerivAlongAt_unitTangent g γ hγ x (himm x))
  have heq : (fun y => g.metricInner (γ y) (curvatureVector g γ y) (unitTangent g γ y)) =
      fun _ => (0 : ℝ) := funext (curvatureVector_orthogonal_of_contMDiff g γ hγ himm)
  rw [heq] at hprod
  have hz := hprod.unique (hasDerivAt_const x (0 : ℝ))
  have hq : curvatureSq g γ x = (curveSpeed g γ x)⁻¹ *
      g.metricInner (γ x) (curvatureVector g γ x)
        (covDerivAlong g γ (unitTangent g γ) x) := by
    unfold curvatureSq
    conv_lhs => arg 4; unfold curvatureVector
    rw [g.metricInner_smul_right]
  unfold covArcDeriv
  rw [g.metricInner_smul_left, hq]
  have hm := congrArg (fun r : ℝ => (curveSpeed g γ x)⁻¹ * r) hz
  nlinarith [hm]

theorem curvatureGradient_norm_decomposition (g : RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) (x : ℝ)
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x
      (covDerivAlong g γ (curvatureVector g γ) x)) :
    g.metricInner (γ x) (covArcDeriv g γ (curvatureVector g γ) x)
      (covArcDeriv g γ (curvatureVector g γ) x) =
      g.metricInner (γ x) (normalCurvatureGradient g γ x) (normalCurvatureGradient g γ x) +
        (curvatureSq g γ x) ^ 2 := by
  unfold normalCurvatureGradient
  simp only [g.metricInner_add_left, g.metricInner_add_right,
    g.metricInner_smul_left, g.metricInner_smul_right,
    g.metricInner_comm (γ x) (unitTangent g γ x)
      (covArcDeriv g γ (curvatureVector g γ) x),
    covArcDeriv_curvature_inner_tangent g γ hγ himm x hD,
    unitTangent_unit g γ x (himm x)]
  ring

theorem normalCurvatureGradient_orthogonal (g : RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) (x : ℝ)
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x
      (covDerivAlong g γ (curvatureVector g γ) x)) :
    g.metricInner (γ x) (normalCurvatureGradient g γ x) (unitTangent g γ x) = 0 := by
  unfold normalCurvatureGradient
  rw [g.metricInner_add_left, g.metricInner_smul_left,
    covArcDeriv_curvature_inner_tangent g γ hγ himm x hD,
    unitTangent_unit g γ x (himm x)]
  ring

/-- **Math.** The Kato conclusion with a scalar nonnegative normal-gradient
norm, directly matching the `P` input of the regularized scalar PDE lemma. -/
theorem curvatureSq_kato_sqrt (g : RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) (x : ℝ)
    (hD : HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) x
      (covDerivAlong g γ (curvatureVector g γ) x)) :
    (Analysis.arcDeriv (curveSpeed g γ) (curvatureSq g γ) x) ^ 2 ≤
      4 * curvatureSq g γ x *
        (Real.sqrt (g.metricInner (γ x) (normalCurvatureGradient g γ x)
          (normalCurvatureGradient g γ x))) ^ 2 := by
  rw [Real.sq_sqrt (g.metricInner_self_nonneg _ _)]
  exact curvatureSq_kato g γ hγ himm x hD

/-- **Math.** Second arclength derivative of squared curvature from actual
covariant metric compatibility. `hD` supplies a genuine first covariant
derivative along the curve; `hDD` supplies one for its arclength derivative. -/
theorem arcDeriv_arcDeriv_curvatureSq (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ)
    (hD : ∀ y, HasCovDerivAlongAt (I := I) g γ (curvatureVector g γ) y
      (covDerivAlong g γ (curvatureVector g γ) y))
    (hDD : HasCovDerivAlongAt (I := I) g γ (covArcDeriv g γ (curvatureVector g γ)) x
      (covDerivAlong g γ (covArcDeriv g γ (curvatureVector g γ)) x)) :
    Analysis.arcDeriv (curveSpeed g γ)
      (Analysis.arcDeriv (curveSpeed g γ) (curvatureSq g γ)) x =
      2 * g.metricInner (γ x) (covArcDeriv g γ (curvatureVector g γ) x)
        (covArcDeriv g γ (curvatureVector g γ) x) +
      2 * g.metricInner (γ x) (covArcDeriv g γ (covArcDeriv g γ (curvatureVector g γ)) x)
        (curvatureVector g γ x) := by
  have heq : Analysis.arcDeriv (curveSpeed g γ) (curvatureSq g γ) =
      fun y => 2 * g.metricInner (γ y) (covArcDeriv g γ (curvatureVector g γ) y)
        (curvatureVector g γ y) :=
    funext fun y => arcDeriv_curvatureSq g γ y (hD y)
  have hd := (hDD.hasDerivAt_metricInner (hD x)).const_mul 2
  rw [heq]
  unfold Analysis.arcDeriv
  rw [hd.deriv]
  simp only [covArcDeriv, g.metricInner_smul_left, g.metricInner_smul_right]
  ring

end CurveControl.Geometry
