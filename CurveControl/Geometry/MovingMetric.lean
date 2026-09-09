import MorganTianLib.Ch02.CovDerivAlongCurve
import MorganTianLib.Ch03.RicciFlow.MetricCoordinateVariation

/-! The metric product rule for genuine tangent fields along a moving manifold
curve and a time dependent smooth Riemannian metric. Joint differentiability is
proved in a chart; the partial derivatives come from metric variation and metric
compatibility, respectively. -/
noncomputable section
open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff
namespace CurveControl.Geometry

/-- **Math.** Restrict a jointly differentiable scalar function to the diagonal. -/
theorem hasDerivAt_diagonal_of_slices {F : ℝ × ℝ → ℝ} {t a b : ℝ}
    (hF : DifferentiableAt ℝ F (t, t))
    (ha : HasDerivAt (fun s => F (s, t)) a t)
    (hb : HasDerivAt (fun s => F (t, s)) b t) :
    HasDerivAt (fun s => F (s, s)) (a + b) t := by
  have h₁ := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (s, t)) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t))
  have h₂ := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (t, s)) t
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t))
  have hd := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (s, s)) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t))
  have h₁' : fderiv ℝ F (t, t) (1, 0) = a := h₁.unique ha
  have h₂' : fderiv ℝ F (t, t) (0, 1) = b := h₂.unique hb
  exact hd.congr_deriv (by
    rw [show ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) by simp, map_add, h₁', h₂'])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Joint differentiability of the actual moving-point metric pairing follows
from joint smoothness of its chart Gram entries and differentiability of the
curve and tangent fields in their actual tangent-bundle trivialization. -/
theorem differentiableAt_metricInner_time_curve
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) {t : ℝ} (ht : t ∈ interior J)
    {γ : ℝ → M} {V W : ∀ r, TangentSpace I (γ r)} {DV DW : E}
    (hV : HasCovDerivAlongAt (I := I) (g t) γ V t DV)
    (hW : HasCovDerivAlongAt (I := I) (g t) γ W t DW) :
    DifferentiableAt ℝ
      (fun z : ℝ × ℝ => (g z.1).metricInner (γ z.2) (V z.2) (W z.2)) (t, t) := by
  classical
  obtain ⟨hmem, v, dV, hu, hv, _⟩ := hV
  obtain ⟨_, _, dW, _, hw, _⟩ := hW
  let u := chartLocalCurve (I := I) γ t
  let vcoord := chartFieldCoord (I := I) (γ t) γ V
  let wcoord := chartFieldCoord (I := I) (γ t) γ W
  have hsrc : γ t ∈ (extChartAt I (γ t)).source := by
    rw [extChartAt_source]
    exact mem_chart_source H (γ t)
  have htarget : u t ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source hsrc
  have hmap : DifferentiableAt ℝ (fun z : ℝ × ℝ => (z.1, u z.2)) (t, t) :=
    differentiableAt_fst.prodMk (hu.differentiableAt.comp (f := fun z : ℝ × ℝ => z.2) (t, t) differentiableAt_snd)
  have hgram (i j : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ
        (fun z : ℝ × ℝ => chartGramOnE (I := I) (g z.1) (γ t) i j (u z.2))
        (t, t) :=
    ((contDiffAt_chartGramOnE_timeSpace hg (γ t) i j ht htarget).differentiableAt
      (by norm_num)).comp (f := fun z : ℝ × ℝ => (z.1, u z.2))
      (g := fun z : ℝ × E => chartGramOnE (I := I) (g z.1) (γ t) i j z.2) (t, t) hmap
  have hvc (i : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ
      (fun z : ℝ × ℝ => chartCoord (E := E) i (vcoord z.2)) (t, t) := by
    exact (chartCoordFunctional (E := E) i).differentiableAt.comp (t, t)
      (hv.differentiableAt.comp (f := fun z : ℝ × ℝ => z.2) (t, t) differentiableAt_snd)
  have hwc (j : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ
      (fun z : ℝ × ℝ => chartCoord (E := E) j (wcoord z.2)) (t, t) := by
    exact (chartCoordFunctional (E := E) j).differentiableAt.comp (t, t)
      (hw.differentiableAt.comp (f := fun z : ℝ × ℝ => z.2) (t, t) differentiableAt_snd)
  have hchart : DifferentiableAt ℝ
      (fun z : ℝ × ℝ => chartMetricInner (I := I) (g z.1) (γ t)
        (u z.2) (vcoord z.2) (wcoord z.2)) (t, t) := by
    simp only [chartMetricInner_def]
    exact DifferentiableAt.fun_sum fun i _ =>
      DifferentiableAt.fun_sum fun j _ => ((hgram i j).mul (hvc i)).mul (hwc j)
  apply hchart.congr_of_eventuallyEq
  have hmem' : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, t), γ z.2 ∈ (chartAt H (γ t)).source :=
    (show Tendsto (fun z : ℝ × ℝ => z.2) (𝓝 (t, t)) (𝓝 t) from
      continuousAt_snd.tendsto).eventually hmem
  filter_upwards [hmem'] with z hz
  exact metricInner_eq_chartMetricInner (I := I) (g z.1) (γ t) hz (V z.2) (W z.2)

/-- **Math.** The moving-metric product rule. The covariant derivatives are taken for
`g t` at the evaluation time. The additional term is the prescribed, genuine
pointwise time variation of the metric, not a postulated moving-curve identity. -/
theorem hasDerivAt_movingMetricInner
    {g : ℝ → Riemannian.RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) {t : ℝ} (ht : t ∈ interior J)
    {γ : ℝ → M} {V W : ∀ r, TangentSpace I (γ r)} {DV DW : E}
    (hV : HasCovDerivAlongAt (I := I) (g t) γ V t DV)
    (hW : HasCovDerivAlongAt (I := I) (g t) γ W t DW) :
    HasDerivAt (fun s => (g s).metricInner (γ s) (V s) (W s))
      (h t (γ t) (V t) (W t) +
        ((g t).metricInner (γ t) DV (W t) + (g t).metricInner (γ t) (V t) DW)) t := by
  exact hasDerivAt_diagonal_of_slices
    (differentiableAt_metricInner_time_curve hg ht hV hW)
    ((hh t (interior_subset ht) (γ t) (V t) (W t)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht))
    (hV.hasDerivAt_metricInner hW)

/-- **Math.** Squared length of an actual tangent field along a moving curve
under Ricci flow. This is the metric-evolution contribution used in the speed
and curvature calculations. -/
theorem hasDerivAt_ricciFlow_field_sq [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J)
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {DV : E}
    (hV : HasCovDerivAlongAt (I := I) (g t) γ V t DV) :
    HasDerivAt (fun s => (g s).metricInner (γ s) (V s) (V s))
      (-2 * ricciTensorAt (g t) (γ t) (V t) (V t) +
        2 * (g t).metricInner (γ t) DV (V t)) t := by
  have hd := hasDerivAt_movingMetricInner hflow.smooth
    (isMetricVariationOn_of_isRicciFlowOn hflow) ht hV hV
  apply hd.congr_deriv
  rw [(g t).metricInner_comm (γ t) (V t) DV]
  ring

#print axioms hasDerivAt_diagonal_of_slices
#print axioms differentiableAt_metricInner_time_curve
#print axioms hasDerivAt_movingMetricInner
#print axioms hasDerivAt_ricciFlow_field_sq
end CurveControl.Geometry
