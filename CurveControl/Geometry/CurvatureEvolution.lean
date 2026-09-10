import CurveControl.Geometry.CurveEvolution
import CurveControl.Geometry.CurveRegularity
import CurveControl.Geometry.AmbientBounds
import CurveControl.Geometry.RicciConnectionVariation
import CurveControl.Geometry.SpeedEvolution
import CurveControl.Geometry.CurvatureGradient
import DoCarmoLib.Riemannian.Connection.CovariantDerivativeAlong
import MorganTianLib.Ch01.CurvatureSectionalBound

/-!
# Actual curve-flow curvature evolution: chart bridges

The coordinate fields in this file are the readbacks of the actual manifold
curve and metric. Chart covariance is proved upstream for the Levi-Civita
connection, and is used here to identify the analytic coordinate operators.
-/
open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
namespace CurveControl.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The bundle-trivialization readback is its tangent coordinate change. -/
theorem chartFieldCoord_eq_tangentCoordChange (α : M) (γ : ℝ → M)
    (W : ∀ s, TangentSpace I (γ s)) (x : ℝ) :
    chartFieldCoord (I := I) α γ W x = tangentCoordChange I (γ x) α (γ x) (W x) := rfl

/-- **Math.** The actual moving-foot derivative agrees with the upstream chart-covariant
Levi-Civita derivative, including its actual tangent-field readback. -/
theorem covDerivAlong_eq_riemannian (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (W : ∀ s, TangentSpace I (γ s)) (x : ℝ) :
    covDerivAlong g γ W x = Riemannian.covDerivAlong (I := I) g γ W x := by
  rw [Riemannian.covDerivAlong_def, covariantDerivCoord_def, chartFieldRep_self]
  rfl

/-- **Math.** Fixed-chart representation of the genuine covariant derivative. -/
theorem chartFieldCoord_covDerivAlong (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (W : ∀ s, TangentSpace I (γ s)) (α : M) {x : ℝ}
    (hc : ContinuousAt γ x) (hα : γ x ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I α (γ s)) x)
    (hW : DifferentiableAt ℝ (chartFieldCoord (I := I) α γ W) x) :
    tangentCoordChange I (γ x) α (γ x) (covDerivAlong g γ W x) =
      covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
        (chartFieldCoord (I := I) α γ W) x := by
  rw [covDerivAlong_eq_riemannian,
    Riemannian.covDerivAlong_eq_chart (I := I) g α hc hα hu hW]
  have hα' : γ x ∈ (extChartAt I α).source := by simpa only [extChartAt_source] using hα
  rw [tangentCoordChange_comp ⟨⟨hα', mem_extChartAt_source (I := I) (γ x)⟩, hα'⟩,
    tangentCoordChange_self hα']
  rfl

/-- **Math.** Genuine covariant differentiability follows from the actual
moving-foot coordinate derivatives. -/
theorem hasCovDerivAlongAt_of_chartDifferentiable (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (W : ∀ s, TangentSpace I (γ s)) (x : ℝ)
    (hγ : ContinuousAt γ x)
    (hu : DifferentiableAt ℝ (chartLocalCurve (I := I) γ x) x)
    (hW : DifferentiableAt ℝ (chartFieldCoord (I := I) (γ x) γ W) x) :
    HasCovDerivAlongAt (I := I) g γ W x (covDerivAlong g γ W x) := by
  refine ⟨hγ ((chartAt H (γ x)).open_source.mem_nhds (mem_chart_source H (γ x))),
    deriv (chartLocalCurve (I := I) γ x) x,
    deriv (chartFieldCoord (I := I) (γ x) γ W) x, hu.hasDerivAt, hW.hasDerivAt, ?_⟩
  rfl

/-- **Math.** Actual scalar rate of arc-length density decay under Ricci flow. -/
def curveSpeedDecay [SigmaCompactSpace M] [T2Space M] (g : ℝ → Riemannian.RiemannianMetric I M) (c : ℝ → ℝ → M)
    (p : ℝ × ℝ) : ℝ :=
  curvatureSq (g p.1) (c p.1) p.2 + ricciTensorAt (g p.1) (c p.1 p.2)
    (unitTangent (g p.1) (c p.1) p.2) (unitTangent (g p.1) (c p.1) p.2)

/-- **Math.** The chart metric at its canonical foot reads the actual metric. -/
theorem chartMetricInner_canonical (g : Riemannian.RiemannianMetric I M)
    (p : M) (U V : E) :
    chartMetricInner (I := I) g p (extChartAt I p p) U V = g.metricInner p U V := by
  simpa only [chartFiberCoord_mk] using
    (metricInner_eq_chartMetricInner (I := I) g p (mem_chart_source H p) U V).symm

/-- **Math.** The intrinsic curvature term with the upstream slot convention;
the do Carmo coordinate sign is canceled by antisymmetry in the last pair. -/
theorem chartCurvature_pairing_canonical [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric I M) (p : M) (U V : E) :
    g.metricInner p (chartCurvature (E := E) (I := I) g p (extChartAt I p p) U V V) U =
      curvatureFormAt g g.leviCivitaConnection p U V U V := by
  have he := curvatureFormAt_chartFrame (I := I) g (α := p) (p := p) (mem_chart_source H p) U V V U
  have hframe (X : E) : (∑ i, chartCoord (E := E) i X • Tensor.chartBasisVecFiber (I := I) p i p) = X := by
    simp only [chartBasisVecFiber_self, chartCoord_def]
    exact (Module.finBasis ℝ E).sum_repr X
  rw [hframe U, hframe V, chartMetricInner_canonical] at he
  have hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hs := curvatureFormAt_antisymm_right g g.leviCivitaConnection hLC.2 p U V V U
  linarith

/-- **Math.** At the canonical foot, inverse tangent trivialization is the identity. -/
theorem tangentReadback_canonical (p : M) (U : E) :
    (trivializationAt E (TangentSpace I) p).symm p U = U := by
  have hh := congrArg Prod.snd ((trivializationAt E (TangentSpace I) p).apply_mk_symm
    (FiberBundle.mem_baseSet_trivializationAt' p) U)
  change chartFiberCoord (I := I) p ⟨p, (trivializationAt E (TangentSpace I) p).symm p U⟩ = U at hh
  rw [chartFiberCoord_mk] at hh
  exact hh

/-- **Math.** Lowering the actual time-varying connection at its canonical foot
produces exactly the two intrinsic covariant-Ricci correction terms. -/
theorem timeVariation_pairing_canonical [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J) (p : M) (S N : E) :
    (g t).metricInner p
      (EvolvingConnection.timeVariation (E := E)
        (fun s => chartChristoffelBilin (I := I) (g s) p) t (extChartAt I p p) S S) N =
      -2 * AmbientBounds.covRic (g t) p S S N + AmbientBounds.covRic (g t) p N S S := by
  have hy : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source (I := I) p)
  have hh := RicciConnectionVariation.deriv_chartChristoffelBilin_lower_intrinsic
    hflow p S S N ht hy
  dsimp only at hh
  rw [(extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)] at hh
  simp only [tangentReadback_canonical] at hh
  change (g t).metricInner p
    (deriv (fun s => chartChristoffelBilin (I := I) (g s) p (extChartAt I p p)) t S S) N = _
  dsimp only [AmbientBounds.covRic]
  linarith

namespace IsCurveShorteningFlowOn
variable {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
  (hc : IsCurveShorteningFlowOn (I := I) g c J)
include hc

/-- **Math.** Actual unit tangent read in one fixed chart. -/
theorem chartUnitTangent_eq (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    tangentCoordChange I (c p.1 p.2) α (c p.1 p.2)
      (unitTangent (g p.1) (c p.1) p.2) =
      CurveEvolution.tangent (chartCurveFamily (I := I) α c)
        (fun z => curveSpeed (g z.1) (c z.1) z.2) p := by
  unfold unitTangent CurveEvolution.tangent
  rw [map_smul]
  congr 1
  exact hc.chartVelocity_eq_spatialFDeriv α hp hα

/-- **Math.** A fixed chart contains the nearby family in the interior time domain. -/
theorem eventually_interior_chart_at (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 p, z.1 ∈ interior J ∧ c z.1 z.2 ∈ (chartAt H α).source := by
  have ht : ∀ᶠ z : ℝ × ℝ in 𝓝 p, z.1 ∈ interior J :=
    continuousAt_fst (isOpen_interior.mem_nhds hp)
  have hs : ∀ᶠ z : ℝ × ℝ in 𝓝 p, c z.1 z.2 ∈ (chartAt H α).source :=
    (hc.contMDiffAt_family hp).continuousAt ((chartAt H α).open_source.mem_nhds hα)
  exact ht.and hs

/-- **Math.** The analytic spatial covariant derivative is the chart readback of the
actual manifold derivative. The representative hypothesis is only a germ
identity for the actual field; no covariant derivative formula is assumed. -/
theorem chart_covSpace_eq (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source)
    (W : ∀ t x, TangentSpace I (c t x)) {V : ℝ × ℝ → E}
    (hV : DifferentiableAt ℝ V p)
    (hrep : (fun z : ℝ × ℝ => tangentCoordChange I (c z.1 z.2) α (c z.1 z.2)
      (W z.1 z.2)) =ᶠ[𝓝 p] V) :
    tangentCoordChange I (c p.1 p.2) α (c p.1 p.2)
      (covDerivAlong (g p.1) (c p.1) (W p.1) p.2) =
      EvolvingConnection.covSpace (fun t => chartChristoffelBilin (I := I) (g t) α)
        (chartCurveFamily (I := I) α c) V p := by
  have hslice : HasDerivAt (fun x : ℝ => (p.1, x)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hu := (hc.contDiffAt_chartCurveFamily α hp hα).differentiableAt (by simp)
  have hud : HasDerivAt (fun y => extChartAt I α (c p.1 y))
      (fderiv ℝ (chartCurveFamily (I := I) α c) p (0, 1)) p.2 := by
    simpa only [Function.comp_def, chartCurveFamily] using
      hu.hasFDerivAt.comp_hasDerivAt p.2 hslice
  have hVd := hV.hasFDerivAt.comp_hasDerivAt p.2 hslice
  have htend : Tendsto (fun x : ℝ => (p.1, x)) (𝓝 p.2) (𝓝 p) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hrep' : chartFieldCoord (I := I) α (c p.1) (W p.1) =ᶠ[𝓝 p.2]
      (fun x => V (p.1, x)) := by
    have he := hrep.comp_tendsto htend
    filter_upwards [he] with y hy
    rw [chartFieldCoord_eq_tangentCoordChange]
    exact hy
  have hW : HasDerivAt (chartFieldCoord (I := I) α (c p.1) (W p.1))
      (fderiv ℝ V p (0, 1)) p.2 := hVd.congr_of_eventuallyEq hrep'
  rw [chartFieldCoord_covDerivAlong (g p.1) (c p.1) (W p.1) α
    (hc.contMDiff_curve (interior_subset hp)).continuous.continuousAt hα
    hud.differentiableAt hW.differentiableAt]
  rw [covariantDerivCoord_def, hW.deriv, hud.deriv, hrep'.eq_of_nhds]
  simp only [EvolvingConnection.covSpace, EvolvingConnection.covDerivAlong,
    EvolvingConnection.coefficients, chartChristoffelBilin_apply, chartCurveFamily]

/-- **Math.** The actual curvature vector is the analytic normal vector in every valid
fixed chart, with actual metric speed as its normalization. -/
theorem chartCurvature_eq_normal (hg : IsSmoothMetricFamilyOn g J)
    (α : M) {p : ℝ × ℝ} (hp : p.1 ∈ interior J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    tangentCoordChange I (c p.1 p.2) α (c p.1 p.2)
      (curvatureVector (g p.1) (c p.1) p.2) =
      CurveEvolution.normal (fun t => chartChristoffelBilin (I := I) (g t) α)
        (chartCurveFamily (I := I) α c)
        (fun z => curveSpeed (g z.1) (c z.1) z.2) p := by
  have hu := hc.contDiffAt_chartCurveFamily α hp hα
  have hv := hc.contDiffAt_curveSpeed hg hp
  have hS := CurveEvolution.tangent_contDiffAt
    (contDiffAt_infty.mp hu 4) (contDiffAt_infty.mp hv 3)
    (ne_of_gt (hc.speed_pos (interior_subset hp) p.2))
  have hrep : (fun z : ℝ × ℝ => tangentCoordChange I (c z.1 z.2) α (c z.1 z.2)
      (unitTangent (g z.1) (c z.1) z.2)) =ᶠ[𝓝 p]
      CurveEvolution.tangent (chartCurveFamily (I := I) α c)
        (fun z => curveSpeed (g z.1) (c z.1) z.2) := by
    filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
    exact hc.chartUnitTangent_eq α hz.1 hz.2
  unfold curvatureVector
  rw [map_smul, hc.chart_covSpace_eq α hp hα
    (fun t => unitTangent (g t) (c t)) (hS.differentiableAt (by norm_num)) hrep]
  rfl

/-- **Math.** Actual curvature has a smooth fixed-chart representative, since
the defining curve-shortening equation identifies it with the time velocity. -/
theorem contDiffAt_chartCurvatureField (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => tangentCoordChange I (c z.1 z.2) α (c z.1 z.2)
      (curvatureVector (g z.1) (c z.1) z.2)) p := by
  have hu := hc.contDiffAt_chartCurveFamily α hp hα
  have hdu : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (chartCurveFamily (I := I) α c) z (1, 0)) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  apply hdu.congr_of_eventuallyEq
  filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
  exact hc.chartCurvature_eq_timeFDeriv α hz.1 hz.2

/-- **Math.** The actual curvature field has a genuine time covariant derivative. -/
theorem hasCovDerivAt_curvature_time {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasCovDerivAlongAt (I := I) (g t) (fun s => c s x)
      (fun s => curvatureVector (g s) (c s) x) t
      (covDerivAlong (g t) (fun s => c s x) (fun s => curvatureVector (g s) (c s) x) t) := by
  have hcurve : ContinuousAt (fun s => c s x) t :=
    (hc.contMDiffAt_family ht).continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  have hH := hc.contDiffAt_chartCurvatureField (c t x) (p := (t, x)) ht (mem_chart_source H _)
  have hd := hH.differentiableAt (by simp)
  apply hasCovDerivAlongAt_of_chartDifferentiable (g t) _ _ t hcurve
    (hc.hasDerivAt_timeChart ht x).differentiableAt
  exact hd.comp (f := fun s : ℝ => (s, x)) t
    (differentiableAt_id.prodMk (differentiableAt_const x))

/-- **Math.** The actual spatial curvature derivative requires no extra
regularity predicate on H beyond the smooth curve-flow input. -/
theorem hasCovDerivAt_curvature_space {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasCovDerivAlongAt (I := I) (g t) (c t) (curvatureVector (g t) (c t)) x
      (covDerivAlong (g t) (c t) (curvatureVector (g t) (c t)) x) := by
  have hcurve := (hc.contMDiff_curve (interior_subset ht)).continuous.continuousAt (x := x)
  have hu := hc.contDiffAt_chartCurveFamily (c t x) (p := (t, x)) ht (mem_chart_source H _)
  have hH := hc.contDiffAt_chartCurvatureField (c t x) (p := (t, x)) ht (mem_chart_source H _)
  apply hasCovDerivAlongAt_of_chartDifferentiable (g t) _ _ x hcurve
  · exact (hu.differentiableAt (by simp)).comp (f := fun y : ℝ => (t, y)) x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  · exact (hH.differentiableAt (by simp)).comp (f := fun y : ℝ => (t, y)) x
      ((differentiableAt_const t).prodMk differentiableAt_id)

/-- **Math.** The proved speed evolution, as the actual joint directional derivative. -/
theorem fderiv_curveSpeed_time [SigmaCompactSpace M] [T2Space M]
    (hflow : IsRicciFlowOn g J) {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    fderiv ℝ (fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2) p (1, 0) =
      -curveSpeedDecay g c p * curveSpeed (g p.1) (c p.1) p.2 := by
  have hv := (hc.contDiffAt_curveSpeed hflow.smooth hp).differentiableAt (by simp)
  have hs : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hd : HasDerivAt (fun s => curveSpeed (g s) (c s) p.2)
      (fderiv ℝ (fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2) p (1, 0)) p.1 :=
    by simpa only [Function.comp_def] using hv.hasFDerivAt.comp_hasDerivAt p.1 hs
  exact hd.unique (hc.hasDerivAt_curveSpeed_time hflow hp p.2)

/-- **Math.** Regularity of the actual speed-decay coefficient is derived from
smooth positive speed and its already proved evolution equation. -/
theorem differentiableAt_curveSpeedDecay [SigmaCompactSpace M] [T2Space M]
    (hflow : IsRicciFlowOn g J) {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    DifferentiableAt ℝ (curveSpeedDecay g c) p := by
  let v := fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2
  have hv := hc.contDiffAt_curveSpeed hflow.smooth hp
  have hvp : v p ≠ 0 := ne_of_gt (hc.speed_pos (interior_subset hp) p.2)
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ v z (1, 0)) p :=
    (((contDiffAt_infty.mp hv 2).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hn : DifferentiableAt ℝ (fun z => -(fderiv ℝ v z (1, 0))) p := hd.neg
  have hvd : DifferentiableAt ℝ v p := hv.differentiableAt (by simp)
  have hregular : DifferentiableAt ℝ (fun z => -(fderiv ℝ v z (1, 0)) / v z) p :=
    by
      change DifferentiableAt ℝ (fun z => -(fderiv ℝ v z (1, 0)) * (v z)⁻¹) p
      exact hn.fun_mul (hvd.fun_inv hvp)
  apply hregular.congr_of_eventuallyEq
  have htime : ∀ᶠ z : ℝ × ℝ in 𝓝 p, z.1 ∈ interior J :=
    continuousAt_fst (isOpen_interior.mem_nhds hp)
  filter_upwards [htime] with z hz
  apply (eq_div_iff (ne_of_gt (hc.speed_pos (interior_subset hz) z.2))).2
  have he := hc.fderiv_curveSpeed_time hflow hz
  change fderiv ℝ v z (1, 0) = -curveSpeedDecay g c z * v z at he
  linarith

/-- **Math.** Actual squared-curvature time derivative from the moving metric
product rule, with the genuine curvature covariant derivative constructed above. -/
theorem hasDerivAt_curvatureSq_time_covariant [SigmaCompactSpace M] [T2Space M]
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasDerivAt (fun s => curvatureSq (g s) (c s) x)
      (-2 * ricciTensorAt (g t) (c t x) (curvatureVector (g t) (c t) x)
          (curvatureVector (g t) (c t) x) +
        2 * (g t).metricInner (c t x)
          (covDerivAlong (g t) (fun s => c s x) (fun s => curvatureVector (g s) (c s) x) t)
          (curvatureVector (g t) (c t) x)) t :=
  hasDerivAt_ricciFlow_field_sq hflow ht (hc.hasCovDerivAt_curvature_time ht x)

/-- **Math.** Curvature-vector evolution in an actual fixed manifold chart.
Every datum is derived from the genuine curve flow and Ricci flow. In particular,
the speed equation, chart normal identity, torsion freedom and coefficient
regularity are conclusions of the preceding geometric lemmas, not new inputs. -/
theorem normal_evolution_in_chart [SigmaCompactSpace M] [T2Space M]
    (hflow : IsRicciFlowOn g J) (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    let Γ := fun t => chartChristoffelBilin (I := I) (g t) α
    let u := chartCurveFamily (I := I) α c
    let v := fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2
    let S := CurveEvolution.tangent u v
    let N := CurveEvolution.normal Γ u v
    EvolvingConnection.covTime Γ u N p =
      CurveEvolution.covArc Γ u v (CurveEvolution.covArc Γ u v N) p
      + (2 * curveSpeedDecay g c p) • N p
      + CurveEvolution.scalarArc v (curveSpeedDecay g c) p • S p
      + EvolvingConnection.curvature Γ p.1 (u p) (N p) (S p) (S p)
      + EvolvingConnection.timeVariation Γ p.1 (u p) (S p) (S p) := by
  let Γ := fun t => chartChristoffelBilin (I := I) (g t) α
  let u := chartCurveFamily (I := I) α c
  let v := fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2
  have hu : ContDiffAt ℝ 4 u p :=
    contDiffAt_infty.mp (hc.contDiffAt_chartCurveFamily α hp hα) 4
  have hv : ContDiffAt ℝ 3 v p :=
    contDiffAt_infty.mp (hc.contDiffAt_curveSpeed hflow.smooth hp) 3
  have hvp : v p ≠ 0 := ne_of_gt (hc.speed_pos (interior_subset hp) p.2)
  have hy : u p ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by simpa only [extChartAt_source] using hα)
  have hΓ : ContDiffAt ℝ 2 (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p) :=
    RicciConnectionVariation.contDiffAt_two_chartChristoffelBilin_timeSpace
      hflow.smooth α hp hy
  have hΓsymm : ∀ᶠ z : ℝ × ℝ in 𝓝 p, ∀ X Y, Γ z.1 (u z) X Y = Γ z.1 (u z) Y X :=
    Eventually.of_forall fun z X Y => chartChristoffelBilin_symm (g z.1) α (u z) X Y
  have hcsf : (fun z => fderiv ℝ u z (1, 0)) =ᶠ[𝓝 p] CurveEvolution.normal Γ u v := by
    filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
    rw [← hc.chartCurvature_eq_timeFDeriv α hz.1 hz.2]
    exact hc.chartCurvature_eq_normal hflow.smooth α hz.1 hz.2
  have hspeed : ∀ᶠ z : ℝ × ℝ in 𝓝 p,
      fderiv ℝ v z (1, 0) = -curveSpeedDecay g c z * v z := by
    filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
    exact hc.fderiv_curveSpeed_time hflow hz.1
  exact CurveEvolution.normal_evolution hu hv hvp
    (hc.differentiableAt_curveSpeedDecay hflow hp) hΓ hΓsymm hcsf hspeed

/-- **Math.** Time analogue of the proved fixed-chart spatial derivative bridge. -/
theorem chart_covTime_eq (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source)
    (W : ∀ t x, TangentSpace I (c t x)) {V : ℝ × ℝ → E}
    (hV : DifferentiableAt ℝ V p)
    (hrep : (fun z : ℝ × ℝ => tangentCoordChange I (c z.1 z.2) α (c z.1 z.2)
      (W z.1 z.2)) =ᶠ[𝓝 p] V) :
    tangentCoordChange I (c p.1 p.2) α (c p.1 p.2)
      (covDerivAlong (g p.1) (fun t => c t p.2) (fun t => W t p.2) p.1) =
      EvolvingConnection.covTime (fun t => chartChristoffelBilin (I := I) (g t) α)
        (chartCurveFamily (I := I) α c) V p := by
  have hslice : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hu := (hc.contDiffAt_chartCurveFamily α hp hα).differentiableAt (by simp)
  have hud : HasDerivAt (fun t => extChartAt I α (c t p.2))
      (fderiv ℝ (chartCurveFamily (I := I) α c) p (1, 0)) p.1 := by
    simpa only [Function.comp_def, chartCurveFamily] using
      hu.hasFDerivAt.comp_hasDerivAt p.1 hslice
  have hVd := hV.hasFDerivAt.comp_hasDerivAt p.1 hslice
  have htend : Tendsto (fun t : ℝ => (t, p.2)) (𝓝 p.1) (𝓝 p) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hrep' : chartFieldCoord (I := I) α (fun t => c t p.2) (fun t => W t p.2) =ᶠ[𝓝 p.1]
      (fun t => V (t, p.2)) := by
    have he := hrep.comp_tendsto htend
    filter_upwards [he] with t ht
    rw [chartFieldCoord_eq_tangentCoordChange]
    exact ht
  have hW : HasDerivAt (chartFieldCoord (I := I) α (fun t => c t p.2) (fun t => W t p.2))
      (fderiv ℝ V p (1, 0)) p.1 := hVd.congr_of_eventuallyEq hrep'
  have hcont : ContinuousAt (fun t => c t p.2) p.1 :=
    (hc.contMDiffAt_family hp).continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  rw [chartFieldCoord_covDerivAlong (g p.1) _ _ α hcont hα hud.differentiableAt hW.differentiableAt]
  rw [covariantDerivCoord_def, hW.deriv, hud.deriv, hrep'.eq_of_nhds]
  simp only [EvolvingConnection.covTime, EvolvingConnection.covDerivAlong,
    EvolvingConnection.coefficients, chartChristoffelBilin_apply, chartCurveFamily]

/-- **Math.** Arc-length differentiation of an actual field in a fixed chart. -/
theorem chart_covArc_eq (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source)
    (W : ∀ t x, TangentSpace I (c t x)) {V : ℝ × ℝ → E}
    (hV : DifferentiableAt ℝ V p)
    (hrep : (fun z : ℝ × ℝ => tangentCoordChange I (c z.1 z.2) α (c z.1 z.2)
      (W z.1 z.2)) =ᶠ[𝓝 p] V) :
    tangentCoordChange I (c p.1 p.2) α (c p.1 p.2)
      (covArcDeriv (g p.1) (c p.1) (W p.1) p.2) =
      CurveEvolution.covArc (fun t => chartChristoffelBilin (I := I) (g t) α)
        (chartCurveFamily (I := I) α c)
        (fun z => curveSpeed (g z.1) (c z.1) z.2) V p := by
  unfold covArcDeriv
  rw [map_smul, hc.chart_covSpace_eq α hp hα W hV hrep]
  rfl

/-- **Math.** The analytic normal of the actual flow is smooth, by its proved
identity with the genuine curvature field read in the same fixed chart. -/
theorem contDiffAt_normal_in_chart (hg : IsSmoothMetricFamilyOn g J)
    (α : M) {p : ℝ × ℝ} (hp : p.1 ∈ interior J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ContDiffAt ℝ ∞ (CurveEvolution.normal
      (fun t => chartChristoffelBilin (I := I) (g t) α)
      (chartCurveFamily (I := I) α c)
      (fun z => curveSpeed (g z.1) (c z.1) z.2)) p := by
  apply (hc.contDiffAt_chartCurvatureField α hp hα).congr_of_eventuallyEq
  filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
  exact (hc.chartCurvature_eq_normal hg α hz.1 hz.2).symm

/-- **Math.** The actual first arc-length derivative of H is read by the
analytic derivative of the proved chart normal. -/
theorem chart_covArcCurvature_eq (hg : IsSmoothMetricFamilyOn g J)
    (α : M) {p : ℝ × ℝ} (hp : p.1 ∈ interior J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    tangentCoordChange I (c p.1 p.2) α (c p.1 p.2)
      (covArcDeriv (g p.1) (c p.1) (curvatureVector (g p.1) (c p.1)) p.2) =
      let Γ := fun t => chartChristoffelBilin (I := I) (g t) α
      let u := chartCurveFamily (I := I) α c
      let v := fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2
      CurveEvolution.covArc Γ u v (CurveEvolution.normal Γ u v) p := by
  apply hc.chart_covArc_eq α hp hα (fun t => curvatureVector (g t) (c t))
    ((hc.contDiffAt_normal_in_chart hg α hp hα).differentiableAt (by simp))
  filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
  exact hc.chartCurvature_eq_normal hg α hz.1 hz.2

/-- **Math.** Regularity of the actual first normal derivative in fixed coordinates. -/
theorem contDiffAt_covArcNormal_in_chart [SigmaCompactSpace M] [T2Space M] (hg : IsSmoothMetricFamilyOn g J)
    (α : M) {p : ℝ × ℝ} (hp : p.1 ∈ interior J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    let Γ := fun t => chartChristoffelBilin (I := I) (g t) α
    let u := chartCurveFamily (I := I) α c
    let v := fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2
    ContDiffAt ℝ 2 (CurveEvolution.covArc Γ u v (CurveEvolution.normal Γ u v)) p := by
  have hu := hc.contDiffAt_chartCurveFamily α hp hα
  have hv := hc.contDiffAt_curveSpeed hg hp
  have hN := hc.contDiffAt_normal_in_chart hg α hp hα
  have hy : chartCurveFamily (I := I) α c p ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by simpa only [extChartAt_source] using hα)
  exact ((contDiffAt_infty.mp hv 2).inv (ne_of_gt (hc.speed_pos (interior_subset hp) p.2))).smul
    (CurveEvolution.covSpace_contDiffAt (contDiffAt_infty.mp hu 3) (contDiffAt_infty.mp hN 3)
      (RicciConnectionVariation.contDiffAt_two_chartChristoffelBilin_timeSpace hg α hp hy))

/-- **Math.** Actual second arc-length normal derivative in the same fixed chart. -/
theorem chart_covArc_covArcCurvature_eq [SigmaCompactSpace M] [T2Space M] (hg : IsSmoothMetricFamilyOn g J)
    (α : M) {p : ℝ × ℝ} (hp : p.1 ∈ interior J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    tangentCoordChange I (c p.1 p.2) α (c p.1 p.2)
      (covArcDeriv (g p.1) (c p.1)
        (covArcDeriv (g p.1) (c p.1) (curvatureVector (g p.1) (c p.1))) p.2) =
      let Γ := fun t => chartChristoffelBilin (I := I) (g t) α
      let u := chartCurveFamily (I := I) α c
      let v := fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2
      CurveEvolution.covArc Γ u v (CurveEvolution.covArc Γ u v (CurveEvolution.normal Γ u v)) p := by
  apply hc.chart_covArc_eq α hp hα
    (fun t => covArcDeriv (g t) (c t) (curvatureVector (g t) (c t)))
    ((hc.contDiffAt_covArcNormal_in_chart hg α hp hα).differentiableAt (by norm_num))
  filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
  exact hc.chart_covArcCurvature_eq hg α hz.1 hz.2

/-- **Math.** The actual arc-length curvature derivative has a C² chart representative. -/
theorem contDiffAt_chartCovArcCurvatureField [SigmaCompactSpace M] [T2Space M] (hg : IsSmoothMetricFamilyOn g J)
    (α : M) {p : ℝ × ℝ} (hp : p.1 ∈ interior J)
    (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => tangentCoordChange I (c z.1 z.2) α (c z.1 z.2)
      (covArcDeriv (g z.1) (c z.1) (curvatureVector (g z.1) (c z.1)) z.2)) p := by
  apply (hc.contDiffAt_covArcNormal_in_chart hg α hp hα).congr_of_eventuallyEq
  filter_upwards [hc.eventually_interior_chart_at α hp hα] with z hz
  exact hc.chart_covArcCurvature_eq hg α hz.1 hz.2

/-- **Math.** Genuine covariant differentiability of DsH, supplied from smooth
flow data to the spatial curvature-gradient identities. -/
theorem hasCovDerivAt_covArcCurvature_space [SigmaCompactSpace M] [T2Space M] (hg : IsSmoothMetricFamilyOn g J)
    {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasCovDerivAlongAt (I := I) (g t) (c t)
      (covArcDeriv (g t) (c t) (curvatureVector (g t) (c t))) x
      (covDerivAlong (g t) (c t) (covArcDeriv (g t) (c t) (curvatureVector (g t) (c t))) x) := by
  have hcurve := (hc.contMDiff_curve (interior_subset ht)).continuous.continuousAt (x := x)
  have hu := hc.contDiffAt_chartCurveFamily (c t x) (p := (t, x)) ht (mem_chart_source H _)
  have hW := hc.contDiffAt_chartCovArcCurvatureField hg (c t x) (p := (t, x)) ht (mem_chart_source H _)
  apply hasCovDerivAlongAt_of_chartDifferentiable (g t) _ _ x hcurve
  · exact (hu.differentiableAt (by simp)).comp (f := fun y : ℝ => (t, y)) x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  · exact (hW.differentiableAt (by norm_num)).comp (f := fun y : ℝ => (t, y)) x
      ((differentiableAt_const t).prodMk differentiableAt_id)

/-- **Math.** The actual second spatial q identity with all regularity predicates
proved from curve-flow and metric smoothness. -/
theorem arcDeriv_arcDeriv_curvatureSq_closed [SigmaCompactSpace M] [T2Space M] (hg : IsSmoothMetricFamilyOn g J)
    {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    Analysis.arcDeriv (curveSpeed (g t) (c t))
      (Analysis.arcDeriv (curveSpeed (g t) (c t)) (curvatureSq (g t) (c t))) x =
      2 * (g t).metricInner (c t x) (covArcDeriv (g t) (c t) (curvatureVector (g t) (c t)) x)
        (covArcDeriv (g t) (c t) (curvatureVector (g t) (c t)) x) +
      2 * (g t).metricInner (c t x)
        (covArcDeriv (g t) (c t) (covArcDeriv (g t) (c t) (curvatureVector (g t) (c t))) x)
        (curvatureVector (g t) (c t) x) :=
  arcDeriv_arcDeriv_curvatureSq (g t) (c t) x
    (hc.hasCovDerivAt_curvature_space ht) (hc.hasCovDerivAt_covArcCurvature_space hg ht x)

/-- **Math.** Actual moving-foot curvature-vector evolution. The diffusion and
vector fields are intrinsic; the curvature and connection-time terms are still
written in the canonical chart, to be lowered by the tensor bridges. -/
theorem curvatureVector_evolution_canonicalChart [SigmaCompactSpace M] [T2Space M]
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    let α := c t x
    let Γ := fun s => chartChristoffelBilin (I := I) (g s) α
    let y := extChartAt I α α
    let S := unitTangent (g t) (c t) x
    let N := curvatureVector (g t) (c t) x
    let R : TangentSpace I (c t x) := EvolvingConnection.curvature (E := E) Γ t y N S S
    let A : TangentSpace I (c t x) := EvolvingConnection.timeVariation (E := E) Γ t y S S
    covDerivAlong (g t) (fun s => c s x) (fun s => curvatureVector (g s) (c s) x) t =
      covArcDeriv (g t) (c t) (covArcDeriv (g t) (c t) (curvatureVector (g t) (c t))) x
      + (2 * curveSpeedDecay g c (t, x)) • N
      + CurveEvolution.scalarArc (fun z => curveSpeed (g z.1) (c z.1) z.2)
          (curveSpeedDecay g c) (t, x) • S
      + R + A := by
  let α := c t x
  let Γ := fun s => chartChristoffelBilin (I := I) (g s) α
  let u := chartCurveFamily (I := I) α c
  let v := fun z : ℝ × ℝ => curveSpeed (g z.1) (c z.1) z.2
  let N := CurveEvolution.normal Γ u v
  let S := CurveEvolution.tangent u v
  have hα : c t x ∈ (chartAt H α).source := mem_chart_source H _
  have hN : DifferentiableAt ℝ N (t, x) :=
    (hc.contDiffAt_normal_in_chart hflow.smooth α ht hα).differentiableAt (by simp)
  have hrep : (fun z : ℝ × ℝ => tangentCoordChange I (c z.1 z.2) α (c z.1 z.2)
      (curvatureVector (g z.1) (c z.1) z.2)) =ᶠ[𝓝 (t, x)] N := by
    filter_upwards [hc.eventually_interior_chart_at α ht hα] with z hz
    exact hc.chartCurvature_eq_normal hflow.smooth α hz.1 hz.2
  have htD := hc.chart_covTime_eq α ht hα (fun s => curvatureVector (g s) (c s)) hN hrep
  have hdiff := hc.chart_covArc_covArcCurvature_eq hflow.smooth α (p := (t, x)) ht hα
  have hN0 := hc.chartCurvature_eq_normal hflow.smooth α (p := (t, x)) ht hα
  have hS0 := hc.chartUnitTangent_eq α (p := (t, x)) ht hα
  have hself (Z : E) : tangentCoordChange I (c t x) α (c t x) Z = Z :=
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (c t x))
  rw [hself] at htD hdiff hN0 hS0
  have he := hc.normal_evolution_in_chart hflow α (p := (t, x)) ht hα
  dsimp only at he hdiff
  rw [← htD, ← hdiff, ← hN0, ← hS0] at he
  exact he

/-- **Math.** The full intrinsic squared-curvature evolution for genuine curve
shortening in a genuine Ricci flow. No scalar or vector evolution equation,
connection variation, mixed-derivative identity or curvature-gradient identity
is assumed as extra input. The normal projection is the spatial one. -/
theorem hasDerivAt_curvatureSq_time [SigmaCompactSpace M] [T2Space M]
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    let S := unitTangent (g t) (c t) x
    let N := curvatureVector (g t) (c t) x
    let P := normalCurvatureGradient (g t) (c t) x
    HasDerivAt (fun s => curvatureSq (g s) (c s) x)
      (Analysis.arcDeriv (curveSpeed (g t) (c t))
          (Analysis.arcDeriv (curveSpeed (g t) (c t)) (curvatureSq (g t) (c t))) x
        - 2 * (g t).metricInner (c t x) P P + 2 * curvatureSq (g t) (c t) x ^ 2
        + ((4 * curvatureSq (g t) (c t) x * ricciTensorAt (g t) (c t x) S S
            - 2 * ricciTensorAt (g t) (c t x) N N
            + 2 * AmbientBounds.rm (g t) (c t x) N S N S)
          + (-4 * AmbientBounds.covRic (g t) (c t x) S S N
            + 2 * AmbientBounds.covRic (g t) (c t x) N S S))) t := by
  have hd := hc.hasDerivAt_curvatureSq_time_covariant hflow ht x
  apply hd.congr_deriv
  have hvec := hc.curvatureVector_evolution_canonicalChart hflow ht x
  dsimp only at hvec ⊢
  rw [hvec]
  simp only [Riemannian.RiemannianMetric.metricInner_add_left,
    Riemannian.RiemannianMetric.metricInner_smul_left]
  have horth : (g t).metricInner (c t x) (unitTangent (g t) (c t) x)
      (curvatureVector (g t) (c t) x) = 0 := by
    rw [(g t).metricInner_comm]
    exact curvatureVector_orthogonal_of_contMDiff (g t) (c t)
      (hc.contMDiff_curve (interior_subset ht)) (hc.immersed t (interior_subset ht)) x
  have hrm : (g t).metricInner (c t x)
      (EvolvingConnection.curvature (E := E)
        (fun s => chartChristoffelBilin (I := I) (g s) (c t x)) t
        (extChartAt I (c t x) (c t x)) (curvatureVector (g t) (c t) x)
        (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x))
      (curvatureVector (g t) (c t) x) =
      AmbientBounds.rm (g t) (c t x) (curvatureVector (g t) (c t) x)
        (unitTangent (g t) (c t) x) (curvatureVector (g t) (c t) x) (unitTangent (g t) (c t) x) :=
    chartCurvature_pairing_canonical (g t) (c t x)
      (curvatureVector (g t) (c t) x) (unitTangent (g t) (c t) x)
  rw [horth, hrm, timeVariation_pairing_canonical hflow ht]
  have hq : (g t).metricInner (c t x) (curvatureVector (g t) (c t) x)
      (curvatureVector (g t) (c t) x) = curvatureSq (g t) (c t) x := rfl
  rw [hq]
  have hspace := hc.arcDeriv_arcDeriv_curvatureSq_closed hflow.smooth ht x
  have hdecomp := curvatureGradient_norm_decomposition (g t) (c t)
    (hc.contMDiff_curve (interior_subset ht)) (hc.immersed t (interior_subset ht)) x
    (hc.hasCovDerivAt_curvature_space ht x)
  rw [hdecomp] at hspace
  dsimp only [curveSpeedDecay]
  nlinarith [hspace]

end IsCurveShorteningFlowOn
end CurveControl.Geometry
