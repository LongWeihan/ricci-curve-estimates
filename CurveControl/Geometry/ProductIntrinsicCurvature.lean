import CurveControl.Geometry.ProductModelCoordinates
import CurveControl.Geometry.ProductChartCurvature
import CurveControl.Geometry.RicciTraceProduct
import CurveControl.Geometry.ProductL2Connection
import CurveControl.Geometry.OneDimensionalCurvature
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality

/-!
# Intrinsic curvature of the genuine Hilbert-model product

The fiber isometry uses each actual Riemannian metric, never the original model
norm. Intrinsic curvature is linked to the actual chart curvature with the
upstream geometric-library sign convention made explicit.
-/

open Set Riemannian Riemannian.Geodesic Riemannian.Jacobi
open scoped Manifold ContDiff Bundle Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** In the chart at the evaluation point the intrinsic curvature
four-form is minus the chart-curvature metric pairing (upstream convention). -/
theorem canonicalCurvatureFormAt_eq_chart (g : RiemannianMetric I M)
    (p : M) (x y z w : TangentSpace I p) :
    g.leviCivitaConnection.curvatureFormAt g p x y z w =
      -chartMetricInner g p (extChartAt I p p)
        (chartCurvature g p (extChartAt I p p) x y z) w := by
  have hh := curvatureFormAt_chartFrame g (α := p) (p := p) (mem_chart_source H p) x y z w
  rw [← trivializationAt_symm_eq_sum_chartBasisVecFiber (I := I) p p x (mem_chart_source H p),
    ← trivializationAt_symm_eq_sum_chartBasisVecFiber (I := I) p p y (mem_chart_source H p),
    ← trivializationAt_symm_eq_sum_chartBasisVecFiber (I := I) p p z (mem_chart_source H p),
    ← trivializationAt_symm_eq_sum_chartBasisVecFiber (I := I) p p w (mem_chart_source H p),
    trivializationAt_symm_self (I := I), trivializationAt_symm_self (I := I),
    trivializationAt_symm_self (I := I), trivializationAt_symm_self (I := I)] at hh
  exact hh

/-- **Math.** The self-chart version with the actual metric pairing. -/
theorem canonicalCurvatureFormAt_eq_metric_chart (g : RiemannianMetric I M)
    (p : M) (x y z w : TangentSpace I p) :
    g.leviCivitaConnection.curvatureFormAt g p x y z w =
      -g.metricInner p (chartCurvature (E := E) (I := I) g p (extChartAt I p p) x y z) w := by
  rw [canonicalCurvatureFormAt_eq_chart,
    chartMetricInner_extChartAt_eq_metricInner _ _ (mem_chart_source H p),
    trivializationAt_symm_self (I := I), trivializationAt_symm_self (I := I)]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [SigmaCompactSpace N] [T2Space N]

/-- **Math.** The L2 product model has nonzero dimension whenever a factor does. -/
instance productL2_finrank_neZero : NeZero (Module.finrank ℝ (WithLp 2 (E × F))) := by
  constructor
  rw [(WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq, Module.finrank_prod]
  have he := NeZero.ne (Module.finrank ℝ E)
  omega

/-- **Math.** The linear splitting of actual product tangent fibers. The target
is the L2 product of the factor fibers, ready for their metric norm instances. -/
def productTangentEquiv (p : M × N) :
    TangentSpace (productL2Model I J) p ≃ₗ[ℝ]
      WithLp 2 (TangentSpace I p.1 × TangentSpace J p.2) :=
  (productL2Equiv (E := E) (F := F)).symm.toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (TangentSpace I p.1 × TangentSpace J p.2)).symm

/-- **Math.** The fiber splitting reads the two model components exactly. -/
theorem productTangentEquiv_apply (p : M × N)
    (x : TangentSpace (productL2Model I J) p) :
    (productTangentEquiv (I := I) (J := J) p x).ofLp = productL2Equiv.symm x := rfl

/-- **Math.** Splitting of the genuine product metric on arbitrary tangent
vectors; this supplies metric preservation for the fiber isometry. -/
theorem productL2Metric_metricInner_split (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (x y : TangentSpace (productL2Model I J) p) :
    (productL2Metric I J g h).metricInner p x y =
      g.metricInner p.1 (productL2Equiv.symm x).1 (productL2Equiv.symm y).1 +
      h.metricInner p.2 (productL2Equiv.symm x).2 (productL2Equiv.symm y).2 := by
  rw [RiemannianMetric.metricInner_apply, productL2Metric_inner_coordinates]
  exact productMetric_inner g h p (productL2Equiv.symm x) (productL2Equiv.symm y)

/-- **Math.** A genuine isometry for the product Riemannian tangent metric,
including the metric-dependent norms on all three fibers. -/
def productTangentIsometry (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (TangentSpace (productL2Model I J) : M × N → Type _) :=
      ⟨(productL2Metric I J g h).toRiemannianMetric⟩
    TangentSpace (productL2Model I J) p ≃ₗᵢ[ℝ]
      WithLp 2 (TangentSpace I p.1 × TangentSpace J p.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (TangentSpace (productL2Model I J) : M × N → Type _) :=
    ⟨(productL2Metric I J g h).toRiemannianMetric⟩
  apply (productTangentEquiv (I := I) (J := J) p).isometryOfInner
  intro x y
  rw [WithLp.prod_inner_apply]
  exact (productL2Metric_metricInner_split g h p x y).symm

/-- **Math.** The canonical intrinsic curvature four-form of the actual L2
product metric is the sum of the two factor curvature four-forms. -/
theorem canonicalCurvatureFormAt_productL2
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (x y z w : TangentSpace (productL2Model I J) p) :
    (productL2Metric I J g h).leviCivitaConnection.curvatureFormAt (productL2Metric I J g h)
        p x y z w =
      g.leviCivitaConnection.curvatureFormAt g p.1
        (productL2Equiv.symm x).1 (productL2Equiv.symm y).1
        (productL2Equiv.symm z).1 (productL2Equiv.symm w).1 +
      h.leviCivitaConnection.curvatureFormAt h p.2
        (productL2Equiv.symm x).2 (productL2Equiv.symm y).2
        (productL2Equiv.symm z).2 (productL2Equiv.symm w).2 := by
  have hcoords : productL2Equiv.symm (extChartAt (productL2Model I J) p p) =
      (extChartAt I p.1 p.1, extChartAt J p.2 p.2) := by
    rw [productL2_extChartAt, ContinuousLinearEquiv.symm_apply_apply, extChartAt_prod]
    rfl
  rw [canonicalCurvatureFormAt_eq_metric_chart,
    chartCurvature_productL2 I J g h p _ x y z (mem_extChartAt_target p),
    productL2Metric_metricInner_split, ContinuousLinearEquiv.symm_apply_apply,
    hcoords, canonicalCurvatureFormAt_eq_metric_chart, canonicalCurvatureFormAt_eq_metric_chart]
  exact neg_add _ _

/-- **Math.** The actual Ricci tensor of the product metric is the sum of the
actual factor Ricci tensors, tracing through the genuine tangent isometry. -/
theorem ricciTensorAt_productL2
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (x y : TangentSpace (productL2Model I J) p) :
    MorganTianLib.ricciTensorAt (productL2Metric I J g h) p x y =
      MorganTianLib.ricciTensorAt g p.1 (productL2Equiv.symm x).1 (productL2Equiv.symm y).1 +
      MorganTianLib.ricciTensorAt h p.2 (productL2Equiv.symm x).2 (productL2Equiv.symm y).2 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (TangentSpace (productL2Model I J) : M × N → Type _) :=
    ⟨(productL2Metric I J g h).toRiemannianMetric⟩
  unfold MorganTianLib.ricciTensorAt
  simp only [Riemannian.ricciBilin_apply]
  exact ricciForm_product _ _ _ (productTangentIsometry g h p)
    (fun u v z w => canonicalCurvatureFormAt_productL2 g h p u v z w) x y

end CurveControl.Geometry

#print axioms CurveControl.Geometry.canonicalCurvatureFormAt_eq_chart
#print axioms CurveControl.Geometry.productTangentEquiv
#print axioms CurveControl.Geometry.productTangentEquiv_apply
#print axioms CurveControl.Geometry.productL2_finrank_neZero
#print axioms CurveControl.Geometry.productL2Metric_metricInner_split
#print axioms CurveControl.Geometry.productTangentIsometry
#print axioms CurveControl.Geometry.canonicalCurvatureFormAt_eq_metric_chart
#print axioms CurveControl.Geometry.canonicalCurvatureFormAt_productL2
#print axioms CurveControl.Geometry.ricciTensorAt_productL2
