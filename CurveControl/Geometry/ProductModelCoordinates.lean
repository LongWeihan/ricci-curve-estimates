import CurveControl.Geometry.ProductModel
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-! Explicit coordinate bridges for the genuine product-model change. -/
open Riemannian Set Filter
open scoped Manifold ContDiff Bundle Topology
noncomputable section
namespace CurveControl.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- **Math.** New extended charts are the old charts followed by the L2 equivalence. -/
theorem productL2_extChartAt (p q : M × N) :
    extChartAt (productL2Model I J) p q =
      productL2Equiv (extChartAt (I.prod J) p q) := rfl

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- **Math.** The inverse chart uses the inverse linear model conversion. -/
theorem productL2_extChartAt_symm (p : M × N) (v : WithLp 2 (E × F)) :
    (extChartAt (productL2Model I J) p).symm v =
      (extChartAt (I.prod J) p).symm (productL2Equiv.symm v) := rfl

variable [I.Boundaryless] [J.Boundaryless]

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- **Math.** The inverse identity diffeomorphism has the expected constant model derivative. -/
theorem productModelInverse_mfderiv (p : M × N) :
    mfderiv (productL2Model I J) (I.prod J)
      (productModelDiffeomorph I J).symm p =
      (productL2Equiv (E := E) (F := F)).symm.toContinuousLinearMap := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuousAt_id, ?_⟩
  have heq : writtenInExtChartAt (productL2Model I J) (I.prod J) p
      (productModelDiffeomorph I J).symm =ᶠ[𝓝 (extChartAt (productL2Model I J) p p)]
      (productL2Equiv (E := E) (F := F)).symm := by
    filter_upwards [extChartAt_target_mem_nhds (I := productL2Model I J) p] with v hv
    change (extChartAt (I.prod J) p)
      ((extChartAt (productL2Model I J) p).symm v) = productL2Equiv.symm v
    have hright := (extChartAt (productL2Model I J) p).right_inv hv
    change productL2Equiv ((extChartAt (I.prod J) p)
      ((extChartAt (productL2Model I J) p).symm v)) = v at hright
    exact (productL2Equiv (E := E) (F := F)).injective (by simpa using hright)
  exact ((productL2Equiv (E := E) (F := F)).symm.hasFDerivAt.congr_of_eventuallyEq
    heq).hasFDerivWithinAt

/-- **Math.** Chart transition derivatives conjugate by the linear model equivalence. -/
theorem productL2_tangentCoordChange (a b p : M × N)
    (hp : p ∈ (extChartAt (I.prod J) a).source ∩ (extChartAt (I.prod J) b).source) :
    tangentCoordChange (productL2Model I J) a b p =
      (productL2Equiv (E := E) (F := F)).toContinuousLinearMap ∘L
        tangentCoordChange (I.prod J) a b p ∘L
        (productL2Equiv (E := E) (F := F)).symm.toContinuousLinearMap := by
  have hbase := hasFDerivWithinAt_tangentCoordChange (I := I.prod J) hp
  rw [ModelWithCorners.range_eq_univ] at hbase
  have hbase' := hbase.hasFDerivAt (by simp)
  have hcomp := (productL2Equiv (E := E) (F := F)).hasFDerivAt.comp
    (extChartAt (productL2Model I J) a p)
    (hbase'.comp (extChartAt (productL2Model I J) a p)
      (productL2Equiv (E := E) (F := F)).symm.hasFDerivAt)
  rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  convert hcomp.fderiv using 1
  congr 1

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Math.** The product metric at a point pairs inverse model coordinates. -/
theorem productL2Metric_inner_coordinates
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u v : TangentSpace (productL2Model I J) p) :
    (productL2Metric I J g h).inner p u v =
      (DCProductMetric g h).inner p (productL2Equiv.symm u) (productL2Equiv.symm v) := by
  rw [productL2Metric_inner, productModelInverse_mfderiv]
  rfl

/-- **Math.** Coordinate changes transport the chart-Gram metric pairing exactly. -/
theorem productL2_chartMetricInner
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a p : M × N) (hp : p ∈ (chartAt (ModelProd H K) a).source)
    (u v : WithLp 2 (E × F)) :
    chartMetricInner (productL2Metric I J g h) a
        (extChartAt (productL2Model I J) a p) u v =
      chartMetricInner (DCProductMetric g h) a
        (extChartAt (I.prod J) a p) (productL2Equiv.symm u) (productL2Equiv.symm v) := by
  rw [chartMetricInner_extChartAt_eq_metricInner _ a hp,
    chartMetricInner_extChartAt_eq_metricInner _ a hp]
  simp only [trivializationAt_symm_eq_tangentCoordChange a hp,
    RiemannianMetric.metricInner_apply]
  rw [productL2Metric_inner_coordinates]
  have hsrc : p ∈ (extChartAt (I.prod J) a).source := by
    rwa [extChartAt_source]
  rw [productL2_tangentCoordChange I J a p p ⟨hsrc, mem_extChartAt_source p⟩]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **Math.** The same exact metric identity over the full valid coordinate target. -/
theorem productL2_chartMetricInner_on_target
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y u v : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    chartMetricInner (productL2Metric I J g h) a y u v =
      chartMetricInner (DCProductMetric g h) a
        (productL2Equiv.symm y) (productL2Equiv.symm u) (productL2Equiv.symm v) := by
  let p := (extChartAt (productL2Model I J) a).symm y
  have hp : p ∈ (chartAt (ModelProd H K) a).source := by
    have hsrc := (extChartAt (productL2Model I J) a).map_target hy
    rwa [extChartAt_source] at hsrc
  have hnew : extChartAt (productL2Model I J) a p = y :=
    (extChartAt (productL2Model I J) a).right_inv hy
  have hold : extChartAt (I.prod J) a p = productL2Equiv.symm y := by
    apply (productL2Equiv (E := E) (F := F)).injective
    simpa only [productL2_extChartAt, ContinuousLinearEquiv.apply_symm_apply] using hnew
  have heq := productL2_chartMetricInner I J g h a p hp u v
  rwa [hnew, hold] at heq

end CurveControl.Geometry
