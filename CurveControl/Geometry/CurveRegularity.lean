import CurveControl.Geometry.ChartBridge
import CurveControl.Geometry.SpatialCurve
import MorganTianLib.Ch03.RicciFlow.MetricCoordinateVariation

/-!
Interior spacetime regularity derived from the genuine smooth metric and curve
flow. Fixed-chart derivatives represent the actual velocity and curvature.
No scalar regularity conclusion is assumed as additional flow data.
-/
open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff
noncomputable section
namespace CurveControl.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- Fixed-chart squared metric norm of a directional derivative of the curve family. -/
def chartDirectionalNormSq (g : ℝ → Riemannian.RiemannianMetric I M) (c : ℝ → ℝ → M)
    (α : M) (d p : ℝ × ℝ) : ℝ :=
  chartMetricInner (I := I) (g p.1) α (chartCurveFamily (I := I) α c p)
    (fderiv ℝ (chartCurveFamily (I := I) α c) p d)
    (fderiv ℝ (chartCurveFamily (I := I) α c) p d)

/-- Differentiation preserves period one, even for the totalized derivative. -/
theorem periodic_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : Function.Periodic f 1) : Function.Periodic (deriv f) 1 := by
  intro x
  rw [← deriv_comp_add_const]
  have heq : (fun y => f (y + 1)) = f := funext hf
  rw [heq]

theorem curveVelocity_periodic (γ : ℝ → M) (hγ : IsClosedCurve γ) :
    Function.Periodic (fun x => (curveVelocity (I := I) γ x : E)) 1 := by
  intro x
  try dsimp only []
  unfold curveVelocity curveVelocityCoord chartLocalCurve
  try dsimp only []
  rw [hγ x]
  exact periodic_deriv (fun y => congrArg (extChartAt I (γ x)) (hγ y)) x

theorem curveSpeed_periodic (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (hγ : IsClosedCurve γ) : Function.Periodic (curveSpeed g γ) 1 := by
  intro x
  try dsimp only []
  unfold curveSpeed
  try simp only [TangentSpace] at *
  simp only [curveVelocity_periodic γ hγ x]
  exact congrArg (fun b : M => Real.sqrt (g.metricInner b
    (curveVelocity (I := I) γ x : E) (curveVelocity (I := I) γ x : E))) (hγ x)

theorem unitTangent_periodic (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (hγ : IsClosedCurve γ) :
    Function.Periodic (fun x => (unitTangent g γ x : E)) 1 := by
  intro x
  try dsimp only []
  unfold unitTangent
  try dsimp only []
  rw [curveSpeed_periodic g γ hγ x]
  exact congrArg (fun v : E => (curveSpeed g γ x)⁻¹ • v) (curveVelocity_periodic γ hγ x)

theorem covDerivAlong_periodic (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (hγ : IsClosedCurve γ) (W : ∀ x, TangentSpace I (γ x))
    (hW : Function.Periodic (fun x => (W x : E)) 1) :
    Function.Periodic (fun x => (covDerivAlong g γ W x : E)) 1 := by
  intro x
  try dsimp only []
  have hf : Function.Periodic (chartFieldCoord (I := I) (γ x) γ W) 1 := by
    intro y
    change tangentCoordChange I (γ (y + 1)) (γ x) (γ (y + 1)) (W (y + 1)) =
      tangentCoordChange I (γ y) (γ x) (γ y) (W y)
    try simp only [TangentSpace] at *
    simp only [hW y, hγ y]
  unfold covDerivAlong
  try dsimp only []
  rw [hγ x, periodic_deriv hf x]
  have hu : Function.Periodic (chartLocalCurve (I := I) γ x) 1 :=
    fun y => congrArg (extChartAt I (γ x)) (hγ y)
  have hh : chartLocalCurve (I := I) γ (x + 1) = chartLocalCurve (I := I) γ x := by
    unfold chartLocalCurve
    rw [hγ x]
  rw [hh, periodic_deriv hu x]
  exact congrArg (fun v : E => deriv (chartFieldCoord (I := I) (γ x) γ W) x +
    chartChristoffelContraction (I := I) g (γ x) (deriv (chartLocalCurve (I := I) γ x) x) v
      (extChartAt I (γ x) (γ x))) (hW x)

theorem curvatureVector_periodic (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (hγ : IsClosedCurve γ) :
    Function.Periodic (fun x => (curvatureVector g γ x : E)) 1 := by
  intro x
  try dsimp only []
  unfold curvatureVector
  try dsimp only []
  rw [curveSpeed_periodic g γ hγ x]
  exact congrArg (fun v : E => (curveSpeed g γ x)⁻¹ • v)
    (covDerivAlong_periodic g γ hγ _ (unitTangent_periodic g γ hγ) x)

theorem curvatureSq_periodic (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (hγ : IsClosedCurve γ) : Function.Periodic (curvatureSq g γ) 1 := by
  intro x
  try dsimp only []
  unfold curvatureSq
  try simp only [TangentSpace] at *
  simp only [curvatureVector_periodic g γ hγ x]
  exact congrArg (fun b : M => g.metricInner b
    (curvatureVector g γ x : E) (curvatureVector g γ x : E)) (hγ x)

theorem regularizedCurvature_periodic (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (hγ : IsClosedCurve γ) (ε : ℝ) :
    Function.Periodic (regularizedCurvature g γ ε) 1 := by
  intro x
  try dsimp only []
  unfold regularizedCurvature
  rw [curvatureSq_periodic g γ hγ x]

/-- Squared norm using the spacetime derivative within the actual time domain. -/
def chartDirectionalNormSqWithin (g : ℝ → Riemannian.RiemannianMetric I M)
    (c : ℝ → ℝ → M) (J : Set ℝ) (α : M) (d p : ℝ × ℝ) : ℝ :=
  chartMetricInner (I := I) (g p.1) α (chartCurveFamily (I := I) α c p)
    (fderivWithin ℝ (chartCurveFamily (I := I) α c) (J ×ˢ (univ : Set ℝ)) p d)
    (fderivWithin ℝ (chartCurveFamily (I := I) α c) (J ×ˢ (univ : Set ℝ)) p d)

/-- Nondegenerate Ricci-flow time intervals have unique within derivatives. -/
theorem uniqueDiffOn_ricciTime [SigmaCompactSpace M] [T2Space M] {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsRicciFlowOn g J) : UniqueDiffOn ℝ J := by
  have hconv : Convex ℝ J := convex_iff_ordConnected.mpr hg.ordConnected
  exact uniqueDiffOn_convex hconv (hconv.nontrivial_iff_nonempty_interior.mp hg.nontrivial)

namespace IsCurveShorteningFlowOn
variable {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
  (hc : IsCurveShorteningFlowOn (I := I) g c J)

include hc

theorem contDiffAt_chartDirectionalNormSq (hg : IsSmoothMetricFamilyOn g J)
    (α : M) (d : ℝ × ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ interior J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ContDiffAt ℝ ∞ (chartDirectionalNormSq g c α d) p := by
  have hu := hc.contDiffAt_chartCurveFamily α hp hα
  have hdu : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (chartCurveFamily (I := I) α c) z d) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hG (i j : Fin (Module.finrank ℝ E)) :
      ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
        chartGramOnE (I := I) (g z.1) α i j (chartCurveFamily (I := I) α c z)) p := by
    have hy : chartCurveFamily (I := I) α c p ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (by simpa only [extChartAt_source] using hα)
    have houter := (contDiffOn_chartGramOnE_timeSpace hg α i j).contDiffAt
      (prod_mem_nhds (mem_interior_iff_mem_nhds.mp hp)
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hy))
    exact houter.comp p (contDiffAt_fst.prodMk hu)
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      ContDiffAt ℝ ∞ (fun z => chartCoord (E := E) i
        (fderiv ℝ (chartCurveFamily (I := I) α c) z d)) p := by
    simpa only [chartCoordFunctional_apply, Function.comp_def] using
      (chartCoordFunctional (E := E) i).contDiff.contDiffAt.comp p hdu
  unfold chartDirectionalNormSq chartMetricInner
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((hG i j).mul (hcoord i)).mul (hcoord j)

theorem curveSpeed_sq_eq_chartDirectionalNormSq (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    curveSpeed (g p.1) (c p.1) p.2 ^ 2 = chartDirectionalNormSq g c α (0, 1) p := by
  rw [curveSpeed_sq, metricInner_eq_chartMetricInner (g p.1) α hα]
  change chartMetricInner (I := I) (g p.1) α (chartCurveFamily (I := I) α c p)
    (chartFieldCoord (I := I) α (c p.1) (curveVelocity (I := I) (c p.1)) p.2)
    (chartFieldCoord (I := I) α (c p.1) (curveVelocity (I := I) (c p.1)) p.2) = _
  rw [hc.chartVelocity_eq_spatialFDeriv α hp hα]
  rfl

theorem curvatureSq_eq_chartDirectionalNormSq (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    curvatureSq (g p.1) (c p.1) p.2 = chartDirectionalNormSq g c α (1, 0) p := by
  unfold curvatureSq
  rw [metricInner_eq_chartMetricInner (g p.1) α hα]
  change chartMetricInner (I := I) (g p.1) α (chartCurveFamily (I := I) α c p)
    (tangentCoordChange I (c p.1 p.2) α (c p.1 p.2) (curvatureVector (g p.1) (c p.1) p.2))
    (tangentCoordChange I (c p.1 p.2) α (c p.1 p.2) (curvatureVector (g p.1) (c p.1) p.2)) = _
  rw [hc.chartCurvature_eq_timeFDeriv α hp hα]
  rfl

theorem eventually_interior_chart {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 p,
      z.1 ∈ interior J ∧ c z.1 z.2 ∈ (chartAt H (c p.1 p.2)).source := by
  have htime : ∀ᶠ z : ℝ × ℝ in 𝓝 p, z.1 ∈ interior J :=
    continuousAt_fst (isOpen_interior.mem_nhds hp)
  have hspace : ∀ᶠ z : ℝ × ℝ in 𝓝 p, c z.1 z.2 ∈ (chartAt H (c p.1 p.2)).source :=
    (hc.contMDiffAt_family hp).continuousAt
      ((chartAt H (c p.1 p.2)).open_source.mem_nhds (mem_chart_source H _))
  exact htime.and hspace

theorem contDiffAt_curveSpeed_sq (hg : IsSmoothMetricFamilyOn g J)
    {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2 ^ 2) p := by
  apply (hc.contDiffAt_chartDirectionalNormSq hg (c p.1 p.2) (0, 1) hp
    (mem_chart_source H _)).congr_of_eventuallyEq
  filter_upwards [hc.eventually_interior_chart hp] with z hz
  exact hc.curveSpeed_sq_eq_chartDirectionalNormSq _ hz.1 hz.2

theorem contDiffAt_curveSpeed (hg : IsSmoothMetricFamilyOn g J)
    {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2) p := by
  have h := (hc.contDiffAt_curveSpeed_sq hg hp).sqrt
    (ne_of_gt (sq_pos_of_pos (hc.speed_pos (interior_subset hp) p.2)))
  simpa only [Real.sqrt_sq (curveSpeed_nonneg _ _ _)] using h

theorem contDiffAt_curvatureSq (hg : IsSmoothMetricFamilyOn g J)
    {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => curvatureSq (g z.1) (c z.1) z.2) p := by
  apply (hc.contDiffAt_chartDirectionalNormSq hg (c p.1 p.2) (1, 0) hp
    (mem_chart_source H _)).congr_of_eventuallyEq
  filter_upwards [hc.eventually_interior_chart hp] with z hz
  exact hc.curvatureSq_eq_chartDirectionalNormSq _ hz.1 hz.2

theorem contDiffAt_regularizedCurvature (hg : IsSmoothMetricFamilyOn g J)
    (ε : ℝ) (hε : 0 < ε) {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => regularizedCurvature (g z.1) (c z.1) ε z.2) p := by
  exact ((hc.contDiffAt_curvatureSq hg hp).add contDiffAt_const).sqrt
    (ne_of_gt (add_pos_of_nonneg_of_pos (curvatureSq_nonneg _ _ _) (sq_pos_of_pos hε)))

/-- Joint coordinate regularity within the time domain, including endpoints. -/
theorem contDiffWithinAt_chartCurveFamily (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ContDiffWithinAt ℝ ∞ (chartCurveFamily (I := I) α c)
      (J ×ˢ (univ : Set ℝ)) p := by
  have h := (contMDiffAt_extChartAt' (I := I) hα).comp_contMDiffWithinAt p
    (hc.smooth p ⟨hp, mem_univ _⟩)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffWithinAt

theorem contDiffWithinAt_chartDirectionalNormSqWithin
    (hg : IsSmoothMetricFamilyOn g J) (hJ : UniqueDiffOn ℝ J)
    (α : M) (d : ℝ × ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ContDiffWithinAt ℝ ∞ (chartDirectionalNormSqWithin g c J α d)
      (J ×ˢ (univ : Set ℝ)) p := by
  have hu := hc.contDiffWithinAt_chartCurveFamily α hp hα
  have hdu := hu.fderivWithin_right_apply (k := fun _ => d) contDiffWithinAt_const
    (hJ.prod uniqueDiffOn_univ) (m := ∞) (by simp) ⟨hp, mem_univ _⟩
  have hG (i j : Fin (Module.finrank ℝ E)) :
      ContDiffWithinAt ℝ ∞ (fun z : ℝ × ℝ =>
        chartGramOnE (I := I) (g z.1) α i j (chartCurveFamily (I := I) α c z))
        (J ×ˢ (univ : Set ℝ)) p := by
    have hy : chartCurveFamily (I := I) α c p ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (by simpa only [extChartAt_source] using hα)
    have houter := contDiffOn_chartGramOnE_timeSpace hg α i j
      (p.1, chartCurveFamily (I := I) α c p) ⟨hp, hy⟩
    have ht : ∀ᶠ z : ℝ × ℝ in 𝓝[J ×ˢ (univ : Set ℝ)] p, z.1 ∈ J :=
      Filter.Eventually.mono self_mem_nhdsWithin (fun _ hz => hz.1)
    have hy' : ∀ᶠ z : ℝ × ℝ in 𝓝[J ×ˢ (univ : Set ℝ)] p,
        chartCurveFamily (I := I) α c z ∈ (extChartAt I α).target :=
      hu.continuousWithinAt ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
    exact houter.comp_of_preimage_mem_nhdsWithin (t := J ×ˢ (extChartAt I α).target) p
      (contDiffWithinAt_fst.prodMk hu) (ht.and hy')
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      ContDiffWithinAt ℝ ∞ (fun z => chartCoord (E := E) i
        (fderivWithin ℝ (chartCurveFamily (I := I) α c) (J ×ˢ (univ : Set ℝ)) z d))
        (J ×ˢ (univ : Set ℝ)) p := by
    simpa only [chartCoordFunctional_apply, Function.comp_def] using
      (chartCoordFunctional (E := E) i).contDiff.contDiffAt.comp_contDiffWithinAt p hdu
  unfold chartDirectionalNormSqWithin chartMetricInner
  exact ContDiffWithinAt.sum fun i _ => ContDiffWithinAt.sum fun j _ =>
    ((hG i j).mul (hcoord i)).mul (hcoord j)

/-- The fixed-chart spatial velocity equals the derivative within spacetime. -/
theorem chartVelocity_eq_spatialFDerivWithin (α : M) {t x : ℝ}
    (ht : t ∈ J) (hα : c t x ∈ (chartAt H α).source) :
    chartFieldCoord (I := I) α (c t) (curveVelocity (I := I) (c t)) x =
      fderivWithin ℝ (chartCurveFamily (I := I) α c) (J ×ˢ (univ : Set ℝ))
        (t, x) (0, 1) := by
  have hc' := hc.contMDiff_curve ht
  have hmem : ∀ᶠ y in 𝓝 x, c t y ∈ (chartAt H α).source :=
    hc'.continuous.continuousAt ((chartAt H α).open_source.mem_nhds hα)
  have hd := (hc.contDiffWithinAt_chartCurveFamily α (p := (t, x)) ht hα).differentiableWithinAt (by simp)
  have hs : HasDerivAt (fun y : ℝ => (t, y)) (0, 1) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  have hh := hd.hasFDerivWithinAt.comp_hasDerivWithinAt x hs.hasDerivWithinAt
    (show MapsTo (fun y : ℝ => (t, y)) univ (J ×ˢ (univ : Set ℝ)) from
      fun _ _ => ⟨ht, mem_univ _⟩)
  exact chartFieldCoord_curveVelocity_eq hmem (hasDerivWithinAt_univ.mp hh)

/-- Time-chart change for the actual endpoint PDE. -/
theorem hasDerivWithinAt_timeChart_in_chart (α : M) {t x : ℝ}
    (ht : t ∈ J) (hα : c t x ∈ (chartAt H α).source) :
    HasDerivWithinAt (fun s => extChartAt I α (c s x))
      (tangentCoordChange I (c t x) α (c t x) (curvatureVector (g t) (c t) x)) J t := by
  have hp : ContinuousWithinAt (fun s => c s x) J t := by
    have hh := hc.smooth.comp
      (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (show MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ (univ : Set ℝ)) from
        fun _ hs => ⟨hs, mem_univ _⟩)
    exact (hh t ht).continuousWithinAt
  have hmem : ∀ᶠ s in 𝓝[J] t, c s x ∈ (chartAt H (c t x)).source :=
    hp ((chartAt H (c t x)).open_source.mem_nhds (mem_chart_source H _))
  have hself : c t x ∈ (extChartAt I (c t x)).source := mem_extChartAt_source _
  have htarget : c t x ∈ (extChartAt I α).source := by simpa only [extChartAt_source] using hα
  have htrans : HasFDerivAt (extChartAt I α ∘ (extChartAt I (c t x)).symm)
      (tangentCoordChange I (c t x) α (c t x)) (extChartAt I (c t x) (c t x)) := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hself, htarget⟩
    rw [I.range_eq_univ] at h
    exact hasFDerivWithinAt_univ.mp h
  refine (htrans.comp_hasDerivWithinAt t (hc.equation t ht x)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hmem] with s hs
    simp only [Function.comp_apply, chartLocalCurve]
    rw [(extChartAt I (c t x)).left_inv (by simpa only [extChartAt_source] using hs)]
  · simp only [Function.comp_apply, chartLocalCurve]
    rw [(extChartAt I (c t x)).left_inv hself]

/-- Curvature is a time derivative within the domain even at an endpoint;
unique time differentiation, not a two-sided extension, identifies its value. -/
theorem chartCurvature_eq_timeFDerivWithin (hJ : UniqueDiffOn ℝ J)
    (α : M) {t x : ℝ} (ht : t ∈ J) (hα : c t x ∈ (chartAt H α).source) :
    tangentCoordChange I (c t x) α (c t x) (curvatureVector (g t) (c t) x) =
      fderivWithin ℝ (chartCurveFamily (I := I) α c) (J ×ˢ (univ : Set ℝ))
        (t, x) (1, 0) := by
  have hd := (hc.contDiffWithinAt_chartCurveFamily α (p := (t, x)) ht hα).differentiableWithinAt (by simp)
  have hs : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hh := hd.hasFDerivWithinAt.comp_hasDerivWithinAt t hs.hasDerivWithinAt
    (show MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ (univ : Set ℝ)) from
      fun _ ht => ⟨ht, mem_univ _⟩)
  exact ((hc.hasDerivWithinAt_timeChart_in_chart α ht hα).derivWithin (hJ t ht)).symm.trans
    (hh.derivWithin (hJ t ht))

theorem curveSpeed_sq_eq_chartDirectionalNormSqWithin (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    curveSpeed (g p.1) (c p.1) p.2 ^ 2 = chartDirectionalNormSqWithin g c J α (0, 1) p := by
  rw [curveSpeed_sq, metricInner_eq_chartMetricInner (g p.1) α hα]
  change chartMetricInner (I := I) (g p.1) α (chartCurveFamily (I := I) α c p)
    (chartFieldCoord (I := I) α (c p.1) (curveVelocity (I := I) (c p.1)) p.2)
    (chartFieldCoord (I := I) α (c p.1) (curveVelocity (I := I) (c p.1)) p.2) = _
  rw [hc.chartVelocity_eq_spatialFDerivWithin α hp hα]
  rfl

theorem curvatureSq_eq_chartDirectionalNormSqWithin (hJ : UniqueDiffOn ℝ J)
    (α : M) {p : ℝ × ℝ} (hp : p.1 ∈ J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    curvatureSq (g p.1) (c p.1) p.2 = chartDirectionalNormSqWithin g c J α (1, 0) p := by
  unfold curvatureSq
  rw [metricInner_eq_chartMetricInner (g p.1) α hα]
  change chartMetricInner (I := I) (g p.1) α (chartCurveFamily (I := I) α c p)
    (tangentCoordChange I (c p.1 p.2) α (c p.1 p.2) (curvatureVector (g p.1) (c p.1) p.2))
    (tangentCoordChange I (c p.1 p.2) α (c p.1 p.2) (curvatureVector (g p.1) (c p.1) p.2)) = _
  rw [hc.chartCurvature_eq_timeFDerivWithin hJ α hp hα]
  rfl

theorem eventually_within_chart {p : ℝ × ℝ} (hp : p.1 ∈ J) :
    ∀ᶠ z : ℝ × ℝ in 𝓝[J ×ˢ (univ : Set ℝ)] p,
      z.1 ∈ J ∧ c z.1 z.2 ∈ (chartAt H (c p.1 p.2)).source := by
  have htime : ∀ᶠ z : ℝ × ℝ in 𝓝[J ×ˢ (univ : Set ℝ)] p, z.1 ∈ J :=
    Filter.Eventually.mono self_mem_nhdsWithin (fun _ hz => hz.1)
  have hspace : ∀ᶠ z : ℝ × ℝ in 𝓝[J ×ˢ (univ : Set ℝ)] p,
      c z.1 z.2 ∈ (chartAt H (c p.1 p.2)).source :=
    (hc.smooth p ⟨hp, mem_univ _⟩).continuousWithinAt
      ((chartAt H (c p.1 p.2)).open_source.mem_nhds (mem_chart_source H _))
  exact htime.and hspace

/-- Actual speed is jointly smooth within the full time domain. -/
theorem contDiffWithinAt_curveSpeed (hg : IsSmoothMetricFamilyOn g J)
    (hJ : UniqueDiffOn ℝ J) {p : ℝ × ℝ} (hp : p.1 ∈ J) :
    ContDiffWithinAt ℝ ∞ (fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2)
      (J ×ˢ (univ : Set ℝ)) p := by
  have hsq : ContDiffWithinAt ℝ ∞
      (fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2 ^ 2)
      (J ×ˢ (univ : Set ℝ)) p := by
    apply (hc.contDiffWithinAt_chartDirectionalNormSqWithin hg hJ (c p.1 p.2) (0, 1) hp
      (mem_chart_source H _)).congr_of_eventuallyEq_of_mem _ ⟨hp, mem_univ _⟩
    filter_upwards [hc.eventually_within_chart hp] with z hz
    exact hc.curveSpeed_sq_eq_chartDirectionalNormSqWithin _ hz.1 hz.2
  have h := hsq.sqrt (ne_of_gt (sq_pos_of_pos (hc.speed_pos hp p.2)))
  simpa only [Real.sqrt_sq (curveSpeed_nonneg _ _ _)] using h

/-- Actual squared curvature is jointly smooth up to included time endpoints. -/
theorem contDiffWithinAt_curvatureSq (hg : IsSmoothMetricFamilyOn g J)
    (hJ : UniqueDiffOn ℝ J) {p : ℝ × ℝ} (hp : p.1 ∈ J) :
    ContDiffWithinAt ℝ ∞ (fun z : ℝ × ℝ => curvatureSq (g z.1) (c z.1) z.2)
      (J ×ˢ (univ : Set ℝ)) p := by
  apply (hc.contDiffWithinAt_chartDirectionalNormSqWithin hg hJ (c p.1 p.2) (1, 0) hp
    (mem_chart_source H _)).congr_of_eventuallyEq_of_mem _ ⟨hp, mem_univ _⟩
  filter_upwards [hc.eventually_within_chart hp] with z hz
  exact hc.curvatureSq_eq_chartDirectionalNormSqWithin hJ _ hz.1 hz.2

theorem contDiffWithinAt_regularizedCurvature (hg : IsSmoothMetricFamilyOn g J)
    (hJ : UniqueDiffOn ℝ J) (ε : ℝ) (hε : 0 < ε) {p : ℝ × ℝ} (hp : p.1 ∈ J) :
    ContDiffWithinAt ℝ ∞ (fun z : ℝ × ℝ => regularizedCurvature (g z.1) (c z.1) ε z.2)
      (J ×ˢ (univ : Set ℝ)) p := by
  exact ((hc.contDiffWithinAt_curvatureSq hg hJ hp).add contDiffWithinAt_const).sqrt
    (ne_of_gt (add_pos_of_nonneg_of_pos (curvatureSq_nonneg _ _ _) (sq_pos_of_pos hε)))

/-- Compact rectangles inherit continuity, including endpoints in J. -/
theorem continuousOn_curveSpeed_rectangle (hg : IsSmoothMetricFamilyOn g J)
    (hJ : UniqueDiffOn ℝ J) {a b : ℝ} (hab : Icc a b ⊆ J) :
    ContinuousOn (fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  intro p hp
  exact (hc.contDiffWithinAt_curveSpeed hg hJ (hab hp.1)).continuousWithinAt.mono
    (fun _ hz => ⟨hab hz.1, mem_univ _⟩)

theorem continuousOn_curvatureSq_rectangle (hg : IsSmoothMetricFamilyOn g J)
    (hJ : UniqueDiffOn ℝ J) {a b : ℝ} (hab : Icc a b ⊆ J) :
    ContinuousOn (fun z : ℝ × ℝ => curvatureSq (g z.1) (c z.1) z.2)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  intro p hp
  exact (hc.contDiffWithinAt_curvatureSq hg hJ (hab hp.1)).continuousWithinAt.mono
    (fun _ hz => ⟨hab hz.1, mem_univ _⟩)

theorem continuousOn_regularizedCurvature_rectangle (hg : IsSmoothMetricFamilyOn g J)
    (hJ : UniqueDiffOn ℝ J) (ε : ℝ) (hε : 0 < ε) {a b : ℝ} (hab : Icc a b ⊆ J) :
    ContinuousOn (fun z : ℝ × ℝ => regularizedCurvature (g z.1) (c z.1) ε z.2)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  intro p hp
  exact (hc.contDiffWithinAt_regularizedCurvature hg hJ ε hε (hab hp.1)).continuousWithinAt.mono
    (fun _ hz => ⟨hab hz.1, mem_univ _⟩)

end IsCurveShorteningFlowOn
end CurveControl.Geometry
