import CurveControl.Geometry.EvolvingConnection
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Coordinate evolution of tangent and curvature

All vector fields below are defined from actual Fréchet derivatives. The only
geometric evolution inputs are curve shortening and the independent speed
identity. Connection commutation is the proved time-dependent identity.
-/
open Filter
open scoped Topology ContDiff
noncomputable section
namespace CurveControl.Geometry.CurveEvolution
open EvolvingConnection
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Arc-length covariant differentiation. -/
def covArc (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E) (u : ℝ × ℝ → E)
    (v : ℝ × ℝ → ℝ) (V : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  (v p)⁻¹ • covSpace Γ u V p

/-- Actual unit tangent when v is the metric speed. -/
def tangent (u : ℝ × ℝ → E) (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : E :=
  (v p)⁻¹ • fderiv ℝ u p (0, 1)

/-- Actual curvature vector for arc-length differentiation. -/
def normal (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E) (u : ℝ × ℝ → E)
    (v : ℝ × ℝ → ℝ) := covArc Γ u v (tangent u v)

def scalarArc (v a : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (v p)⁻¹ * fderiv ℝ a p (0, 1)

theorem covDerivAlong_congr {A : P → E →L[ℝ] E →L[ℝ] E} {u V W : P → E}
    {p : P} (h : V =ᶠ[𝓝 p] W) (d : P) :
    covDerivAlong A u V d p = covDerivAlong A u W d p := by
  simp only [covDerivAlong, h.fderiv_eq, h.eq_of_nhds]

theorem covDerivAlong_smul {A : P → E →L[ℝ] E →L[ℝ] E} {u V : P → E}
    {f : P → ℝ} {p : P} (hf : DifferentiableAt ℝ f p)
    (hV : DifferentiableAt ℝ V p) (d : P) :
    covDerivAlong A u (fun q => f q • V q) d p =
      (fderiv ℝ f p d) • V p + f p • covDerivAlong A u V d p := by
  simp only [covDerivAlong, fderiv_fun_smul hf hV, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    map_smul, smul_add]
  abel

theorem covDerivAlong_add {A : P → E →L[ℝ] E →L[ℝ] E} {u V W : P → E}
    {p : P} (hV : DifferentiableAt ℝ V p) (hW : DifferentiableAt ℝ W p) (d : P) :
    covDerivAlong A u (fun q => V q + W q) d p =
      covDerivAlong A u V d p + covDerivAlong A u W d p := by
  simp only [covDerivAlong, fderiv_fun_add hV hW, add_apply, map_add]
  abel

/-- Inverse-speed derivative follows from the actual scalar chain rule. -/
theorem inverse_speed_time {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {a : ℝ}
    (hv : DifferentiableAt ℝ v p) (hvp : v p ≠ 0)
    (hevol : fderiv ℝ v p (1, 0) = -a * v p) :
    fderiv ℝ (fun q => (v q)⁻¹) p (1, 0) = a * (v p)⁻¹ := by
  have h := (hasDerivAt_inv hvp).comp_hasFDerivAt p hv.hasFDerivAt
  rw [show fderiv ℝ (fun q => (v q)⁻¹) p = _ from h.fderiv]
  simp only [smul_apply, smul_eq_mul, hevol]
  field_simp

/-- Evolution of S, using Schwarz symmetry and torsion-freeness, not an
assumed evolution equation for S. The curve-shortening identity holds as a germ. -/
theorem tangent_evolution {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u : ℝ × ℝ → E} {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {a : ℝ}
    (hu : ContDiffAt ℝ 2 u p) (hv : DifferentiableAt ℝ v p) (hvp : v p ≠ 0)
    (hΓsymm : ∀ X Y, Γ p.1 (u p) X Y = Γ p.1 (u p) Y X)
    (hflow : (fun q => fderiv ℝ u q (1, 0)) =ᶠ[𝓝 p] normal Γ u v)
    (hspeed : fderiv ℝ v p (1, 0) = -a * v p) :
    covTime Γ u (tangent u v) p = covArc Γ u v (normal Γ u v) p + a • tangent u v p := by
  have hux : DifferentiableAt ℝ (fun q => fderiv ℝ u q (0, 1)) p :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  change covDerivAlong (coefficients Γ u) u
    (fun q => (v q)⁻¹ • fderiv ℝ u q (0, 1)) (1, 0) p = _
  rw [covDerivAlong_smul (f := fun q => (v q)⁻¹) (hv.inv hvp) hux, inverse_speed_time hv hvp hspeed]
  rw [covDerivAlong_fderiv_symm hu hΓsymm (1, 0) (0, 1)]
  rw [covDerivAlong_congr hflow (0, 1)]
  simp only [covArc, tangent, covSpace, mul_smul]
  abel

/-- Smoothness of the actual normalized tangent is derived from u and v. -/
theorem tangent_contDiffAt {u : ℝ × ℝ → E} {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 4 u p) (hv : ContDiffAt ℝ 3 v p) (hvp : v p ≠ 0) :
    ContDiffAt ℝ 3 (tangent u v) p :=
  (hv.inv hvp).smul ((hu.fderiv_right (m := 3) (by norm_num)).clm_apply contDiffAt_const)

/-- Regularity of the actual coefficient pullback. -/
theorem coefficients_contDiffAt {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u : ℝ × ℝ → E} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 2 u p)
    (hΓ : ContDiffAt ℝ 2 (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p)) :
    ContDiffAt ℝ 2 (coefficients Γ u) p :=
  ContDiffAt.comp (f := fun q : ℝ × ℝ => (q.1, u q))
    (g := fun z : ℝ × E => Γ z.1 z.2) p hΓ (contDiffAt_fst.prodMk hu)

/-- Regularity for differentiating the spatial covariant derivative once more. -/
theorem covSpace_contDiffAt {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u V : ℝ × ℝ → E} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 3 u p) (hV : ContDiffAt ℝ 3 V p)
    (hΓ : ContDiffAt ℝ 2 (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p)) :
    ContDiffAt ℝ 2 (covSpace Γ u V) p := by
  have hA := coefficients_contDiffAt (hu.of_le (by norm_num)) hΓ
  exact ((hV.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).add
    ((hA.clm_apply ((hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const)).clm_apply
      (hV.of_le (by norm_num)))

/-- Curvature-vector C² regularity is derived, not supplied as geometric data. -/
theorem normal_contDiffAt {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u : ℝ × ℝ → E} {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 4 u p) (hv : ContDiffAt ℝ 3 v p) (hvp : v p ≠ 0)
    (hΓ : ContDiffAt ℝ 2 (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p)) :
    ContDiffAt ℝ 2 (normal Γ u v) p :=
  ((hv.of_le (by norm_num)).inv hvp).smul
    (covSpace_contDiffAt (hu.of_le (by norm_num)) (tangent_contDiffAt hu hv hvp) hΓ)

theorem curvature_smul_second (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E)
    (t : ℝ) (x X Y Z : E) (c : ℝ) :
    curvature Γ t x X (c • Y) Z = c • curvature Γ t x X Y Z := by
  simp only [curvature, map_smul, smul_apply, smul_sub, smul_add]

/-- Commuting time with the genuine arc-length derivative includes the speed
variation term and the explicit time derivative of the spatial connection. -/
theorem covTime_covArc_comm {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u V : ℝ × ℝ → E} {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {a : ℝ}
    (hu : ContDiffAt ℝ 3 u p) (hV : ContDiffAt ℝ 3 V p)
    (hv : DifferentiableAt ℝ v p) (hvp : v p ≠ 0)
    (hΓ : ContDiffAt ℝ 2 (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p))
    (hspeed : fderiv ℝ v p (1, 0) = -a * v p) :
    covTime Γ u (covArc Γ u v V) p = covArc Γ u v (covTime Γ u V) p
      + a • covArc Γ u v V p
      + curvature Γ p.1 (u p) (fderiv ℝ u p (1, 0)) (tangent u v p) (V p)
      + timeVariation Γ p.1 (u p) (tangent u v p) (V p) := by
  have hdx := (covSpace_contDiffAt hu hV hΓ).differentiableAt (by norm_num)
  change covDerivAlong (coefficients Γ u) u
    (fun q => (v q)⁻¹ • covSpace Γ u V q) (1, 0) p = _
  rw [covDerivAlong_smul (f := fun q => (v q)⁻¹) (hv.inv hvp) hdx,
    inverse_speed_time hv hvp hspeed]
  have hc := covTime_covSpace_comm (hu.of_le (by norm_num)) (hV.of_le (by norm_num))
    (hΓ.differentiableAt (by norm_num))
  have he := eq_add_of_sub_eq hc
  change covTime Γ u (covSpace Γ u V) p = _ at he
  change (a * (v p)⁻¹) • covSpace Γ u V p +
    (v p)⁻¹ • covTime Γ u (covSpace Γ u V) p = _
  rw [he]
  simp only [covArc, tangent, curvature_smul_second, map_smul, smul_apply, smul_add, mul_smul]
  abel

/-- C² vector fields have differentiable spatial covariant derivative. -/
theorem covSpace_differentiableAt {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u V : ℝ × ℝ → E} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 2 u p) (hV : ContDiffAt ℝ 2 V p)
    (hΓ : ContDiffAt ℝ 2 (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p)) :
    DifferentiableAt ℝ (covSpace Γ u V) p := by
  have hA := (coefficients_contDiffAt hu hΓ).differentiableAt (by norm_num)
  have hdu := ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := (0, 1)))).differentiableAt (by norm_num)
  have hdV := ((hV.fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := (0, 1)))).differentiableAt (by norm_num)
  exact hdV.add ((hA.clm_apply hdu).clm_apply (hV.differentiableAt (by norm_num)))

/-- Local curvature-vector evolution. All regularity of S and H is obtained
from the displayed smooth data; the two germ evolution inputs concern only
u and speed v. This identity retains the explicit evolving-connection term. -/
theorem normal_evolution {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u : ℝ × ℝ → E} {v a : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 4 u p) (hv : ContDiffAt ℝ 3 v p) (hvp : v p ≠ 0)
    (ha : DifferentiableAt ℝ a p)
    (hΓ : ContDiffAt ℝ 2 (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p))
    (hΓsymm : ∀ᶠ q in 𝓝 p, ∀ X Y, Γ q.1 (u q) X Y = Γ q.1 (u q) Y X)
    (hflow : (fun q => fderiv ℝ u q (1, 0)) =ᶠ[𝓝 p] normal Γ u v)
    (hspeed : ∀ᶠ q in 𝓝 p, fderiv ℝ v q (1, 0) = -a q * v q) :
    covTime Γ u (normal Γ u v) p =
      covArc Γ u v (covArc Γ u v (normal Γ u v)) p
      + (2 * a p) • normal Γ u v p
      + scalarArc v a p • tangent u v p
      + curvature Γ p.1 (u p) (normal Γ u v p) (tangent u v p) (tangent u v p)
      + timeVariation Γ p.1 (u p) (tangent u v p) (tangent u v p) := by
  have hu2 : ContDiffAt ℝ 2 u p := hu.of_le (by norm_num)
  have hu3 : ContDiffAt ℝ 3 u p := hu.of_le (by norm_num)
  have hv1 := hv.differentiableAt (by norm_num)
  have hS3 := tangent_contDiffAt hu hv hvp
  have hH2 := normal_contDiffAt hu hv hvp hΓ
  have hS1 := hS3.differentiableAt (by norm_num)
  have hDsH : DifferentiableAt ℝ (covArc Γ u v (normal Γ u v)) p :=
    (hv1.inv hvp).smul (covSpace_differentiableAt hu2 hH2 hΓ)
  have hnear : covTime Γ u (tangent u v) =ᶠ[𝓝 p]
      (fun q => covArc Γ u v (normal Γ u v) q + a q • tangent u v q) := by
    have hureg := hu.eventually (by norm_num)
    have hvreg := hv.eventually (by norm_num)
    have hvnz := hv.continuousAt.eventually_ne hvp
    filter_upwards [hureg, hvreg, hvnz, hΓsymm, hflow.eventually_nhds, hspeed]
      with q huq hvq hvnq hΓq hflowq hspeedq
    exact tangent_evolution (huq.of_le (by norm_num))
      (hvq.differentiableAt (by norm_num)) hvnq hΓq hflowq hspeedq
  have hcomm := covTime_covArc_comm hu3 hS3 hv1 hvp hΓ (hspeed.self_of_nhds)
  change covTime Γ u (normal Γ u v) p = _ at hcomm
  rw [hflow.eq_of_nhds] at hcomm
  rw [hcomm]
  have hrewrite : covArc Γ u v (covTime Γ u (tangent u v)) p =
      covArc Γ u v (covArc Γ u v (normal Γ u v)) p
      + scalarArc v a p • tangent u v p + a p • normal Γ u v p := by
    change (v p)⁻¹ • covDerivAlong (coefficients Γ u) u
      (covTime Γ u (tangent u v)) (0, 1) p = _
    rw [covDerivAlong_congr hnear (0, 1),
      covDerivAlong_add (W := fun q => a q • tangent u v q) hDsH (ha.smul hS1),
      covDerivAlong_smul ha hS1]
    change (v p)⁻¹ • (covDerivAlong (coefficients Γ u) u
        (covArc Γ u v (normal Γ u v)) (0, 1) p +
      (fderiv ℝ a p (0, 1) • tangent u v p +
        a p • covDerivAlong (coefficients Γ u) u (tangent u v) (0, 1) p)) =
      (v p)⁻¹ • covDerivAlong (coefficients Γ u) u
        (covArc Γ u v (normal Γ u v)) (0, 1) p +
      ((v p)⁻¹ * fderiv ℝ a p (0, 1)) • tangent u v p +
      a p • ((v p)⁻¹ • covDerivAlong (coefficients Γ u) u (tangent u v) (0, 1) p)
    simp only [smul_add, mul_smul]
    rw [smul_comm (v p)⁻¹ (a p)]
    abel
  rw [hrewrite]
  change _ + a p • normal Γ u v p + _ + _ = _
  simp only [show (2 : ℝ) * a p = a p + a p by ring, add_smul]
  abel

end CurveControl.Geometry.CurveEvolution
