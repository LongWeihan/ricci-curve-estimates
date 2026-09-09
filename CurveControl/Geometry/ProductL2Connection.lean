import CurveControl.Geometry.ProductModelCoordinates
import CurveControl.Geometry.ProductChartCurvature

/-! The actual Christoffel contraction under the linear L2 model change.
The proof differentiates the transported Gram form and uses Koszul uniqueness. -/
open Riemannian Riemannian.Geodesic Riemannian.Jacobi Set Filter
open scoped Manifold ContDiff Bundle Topology
noncomputable section
namespace CurveControl.Geometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [IsManifold I ∞ M] [IsManifold J ∞ N] [I.Boundaryless] [J.Boundaryless]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Math.** The L2 target maps back into the original product-chart target. -/
theorem productL2_target_inverse (a : M × N) (y : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    productL2Equiv.symm y ∈ (extChartAt (I.prod J) a).target := by
  simpa only [productL2Model,
    ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage] using hy

/-- **Math.** The transported candidate satisfies the actual metric-compatibility identity. -/
theorem productL2_connection_metric_balance
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u v : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    let e := productL2Equiv (E := E) (F := F)
    let G := chartMetricInner (productL2Metric I J g h) a y
    let B := fun z w => e (chartChristoffelContraction (DCProductMetric g h) a
      (e.symm z) (e.symm w) (e.symm y))
    G (chartChristoffelContraction (productL2Metric I J g h) a x u y) v +
      G u (chartChristoffelContraction (productL2Metric I J g h) a x v y) =
      G (B x u) v + G u (B x v) := by
  dsimp only
  have hd := chartMetricInner_line_hasDerivAt (productL2Metric I J g h) a y x u v hy
  have ho := chartMetricInner_line_hasDerivAt (DCProductMetric g h) a
    (productL2Equiv.symm y) (productL2Equiv.symm x)
    (productL2Equiv.symm u) (productL2Equiv.symm v)
    (productL2_target_inverse I J a y hy)
  have hline : ContinuousAt (fun r : ℝ => y + r • x) 0 := by fun_prop
  have hn : ∀ᶠ r : ℝ in 𝓝 0, y + r • x ∈
      (extChartAt (productL2Model I J) a).target :=
    hline (by simpa using (isOpen_extChartAt_target a).mem_nhds hy)
  have heq : (fun r : ℝ => chartMetricInner (productL2Metric I J g h) a
      (y + r • x) u v) =ᶠ[𝓝 0]
      (fun r : ℝ => chartMetricInner (DCProductMetric g h) a
        (productL2Equiv.symm y + r • productL2Equiv.symm x)
        (productL2Equiv.symm u) (productL2Equiv.symm v)) := by
    filter_upwards [hn] with r hr
    rw [productL2_chartMetricInner_on_target I J g h a _ u v hr]
    simp only [map_add, map_smul]
  have he := hd.unique (ho.congr_of_eventuallyEq heq)
  simpa only [productL2_chartMetricInner_on_target I J g h a y _ _ hy,
    ContinuousLinearEquiv.symm_apply_apply] using he

/-- **Math.** Actual Christoffel contraction conjugates under the linear model change. -/
theorem chartChristoffelContraction_productL2_transport
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    chartChristoffelContraction (productL2Metric I J g h) a x u y =
      productL2Equiv (chartChristoffelContraction (DCProductMetric g h) a
        (productL2Equiv.symm x) (productL2Equiv.symm u) (productL2Equiv.symm y)) := by
  have hsym : ∀ v w, chartMetricInner (productL2Metric I J g h) a y v w =
      chartMetricInner (productL2Metric I J g h) a y w v := by
    intro v w
    unfold chartMetricInner
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [chartGramOnE_symm (productL2Metric I J g h) a j i]
    ring
  have hh := connectionCoefficient_unique
    (chartMetricInner (productL2Metric I J g h) a y)
    (fun v w => chartChristoffelContraction (productL2Metric I J g h) a v w y)
    (fun v w => productL2Equiv (chartChristoffelContraction (DCProductMetric g h) a
      (productL2Equiv.symm v) (productL2Equiv.symm w) (productL2Equiv.symm y))) hsym
    (chartMetricInner_separates (productL2Metric I J g h) a y hy)
    (fun v w => chartChristoffelContraction_symm (productL2Metric I J g h) a v w y)
    (fun v w => congrArg productL2Equiv (chartChristoffelContraction_symm
      (DCProductMetric g h) a (productL2Equiv.symm v) (productL2Equiv.symm w)
      (productL2Equiv.symm y)))
    (fun v w z => productL2_connection_metric_balance I J g h a y v w z hy)
  exact congrFun (congrFun hh x) u

/-- **Math.** The legitimate Hilbert-model product connection splits into its two factors. -/
theorem chartChristoffelContraction_productL2
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    chartChristoffelContraction (productL2Metric I J g h) a x u y =
      productL2Equiv
        (chartChristoffelContraction g a.1 (productL2Equiv.symm x).1
          (productL2Equiv.symm u).1 (productL2Equiv.symm y).1,
         chartChristoffelContraction h a.2 (productL2Equiv.symm x).2
          (productL2Equiv.symm u).2 (productL2Equiv.symm y).2) := by
  rw [chartChristoffelContraction_productL2_transport I J g h a y x u hy]
  exact congrArg productL2Equiv (chartChristoffelContraction_product g h a
    (productL2Equiv.symm y) (productL2Equiv.symm x) (productL2Equiv.symm u)
    (productL2_target_inverse I J a y hy))
/-- **Math.** The actual bilinear Christoffel map transports pointwise. -/
theorem chartChristoffelBilin_productL2_transport
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y u v : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    chartChristoffelBilin (productL2Metric I J g h) a y u v =
      productL2Equiv (chartChristoffelBilin (DCProductMetric g h) a
        (productL2Equiv.symm y) (productL2Equiv.symm u) (productL2Equiv.symm v)) := by
  simp only [chartChristoffelBilin_apply_normed]
  exact chartChristoffelContraction_productL2_transport I J g h a y u v hy

/-- **Math.** Differentiating the proved connection transport along coordinate lines. -/
theorem fderiv_chartChristoffelBilin_productL2_transport
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u v : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    fderiv ℝ (chartChristoffelBilin (productL2Metric I J g h) a) y x u v =
      productL2Equiv (fderiv ℝ (chartChristoffelBilin (DCProductMetric g h) a)
        (productL2Equiv.symm y) (productL2Equiv.symm x)
        (productL2Equiv.symm u) (productL2Equiv.symm v)) := by
  have hd := chartChristoffelBilin_line_hasDerivAt (productL2Metric I J g h) a y x u v hy
  have ho := chartChristoffelBilin_line_hasDerivAt (DCProductMetric g h) a
    (productL2Equiv.symm y) (productL2Equiv.symm x)
    (productL2Equiv.symm u) (productL2Equiv.symm v)
    (productL2_target_inverse I J a y hy)
  have ht := (productL2Equiv (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ho
  have hline : ContinuousAt (fun r : ℝ => y + r • x) 0 := by fun_prop
  have hn : ∀ᶠ r : ℝ in 𝓝 0, y + r • x ∈
      (extChartAt (productL2Model I J) a).target :=
    hline (by simpa using (isOpen_extChartAt_target a).mem_nhds hy)
  have heq : (fun r : ℝ => chartChristoffelBilin (productL2Metric I J g h) a
      (y + r • x) u v) =ᶠ[𝓝 0]
      (fun r : ℝ => productL2Equiv (chartChristoffelBilin (DCProductMetric g h) a
        (productL2Equiv.symm y + r • productL2Equiv.symm x)
        (productL2Equiv.symm u) (productL2Equiv.symm v))) := by
    filter_upwards [hn] with r hr
    rw [chartChristoffelBilin_productL2_transport I J g h a _ u v hr]
    simp only [map_add, map_smul]
  exact hd.unique (ht.congr_of_eventuallyEq heq)

/-- **Math.** Actual chart curvature conjugates under the linear Hilbert model change. -/
theorem chartCurvature_productL2_transport
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u v : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    chartCurvature (productL2Metric I J g h) a y x u v =
      productL2Equiv (chartCurvature (DCProductMetric g h) a
        (productL2Equiv.symm y) (productL2Equiv.symm x)
        (productL2Equiv.symm u) (productL2Equiv.symm v)) := by
  unfold chartCurvature christoffelCurvature
  simp only [fderiv_chartChristoffelBilin_productL2_transport I J g h a y _ _ _ hy,
    chartChristoffelBilin_productL2_transport I J g h a y _ _ hy,
    ContinuousLinearEquiv.symm_apply_apply, map_add, map_sub]

/-- **Math.** Actual curvature in the legitimate L2 model splits into factor curvatures. -/
theorem chartCurvature_productL2
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u v : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    chartCurvature (productL2Metric I J g h) a y x u v =
      productL2Equiv
        (chartCurvature g a.1 (productL2Equiv.symm y).1 (productL2Equiv.symm x).1
          (productL2Equiv.symm u).1 (productL2Equiv.symm v).1,
         chartCurvature h a.2 (productL2Equiv.symm y).2 (productL2Equiv.symm x).2
          (productL2Equiv.symm u).2 (productL2Equiv.symm v).2) := by
  rw [chartCurvature_productL2_transport I J g h a y x u v hy]
  exact congrArg productL2Equiv (chartCurvature_product g h a
    (productL2Equiv.symm y) (productL2Equiv.symm x) (productL2Equiv.symm u)
    (productL2Equiv.symm v) (productL2_target_inverse I J a y hy))
end CurveControl.Geometry
