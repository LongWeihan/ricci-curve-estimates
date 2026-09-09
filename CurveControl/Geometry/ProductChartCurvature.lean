import CurveControl.Geometry.ProductConnection
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureVector

/-!
# Actual chart curvature of the product metric

The bilinear Christoffel map and its derivative split because the actual
Christoffel contraction splits on an open chart target. Substitution in the
upstream curvature definition proves the product curvature identity.
The normed chart models need no inner-product-space structure.
-/

open Set Riemannian Riemannian.Geodesic Riemannian.Jacobi
open scoped ContDiff Manifold Topology

noncomputable section

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The upstream bilinear-map packaging agrees with its contraction,
without requiring an inner-product norm on the chart model. -/
theorem chartChristoffelBilin_apply_normed (g : RiemannianMetric I M) (a : M)
    (y u v : E) : chartChristoffelBilin g a y u v = chartChristoffelContraction g a u v y := by
  simp only [chartChristoffelBilin, chartChristoffelContraction,
    sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply, chartCoordFunctional_apply,
    Finset.sum_smul, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ring

/-- **Math.** Smoothness of the actual bilinear Christoffel map on the interior
chart target, valid for arbitrary finite-dimensional normed models. -/
theorem contDiffOn_chartChristoffelBilin_normed (g : RiemannianMetric I M) (a : M) :
    ContDiffOn ℝ ∞ (chartChristoffelBilin g a) (interior (extChartAt I a).target) := by
  unfold chartChristoffelBilin
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
  have hc : ContDiffOn ℝ ∞ (fun y => chartChristoffel g a i j k y • Module.finBasis ℝ E k)
      (interior (extChartAt I a).target) :=
    (chartChristoffel_contDiffOn_interior g a i j k).smul contDiffOn_const
  exact contDiffOn_const.smulRight (contDiffOn_const.smulRight hc)

variable [I.Boundaryless]

/-- **Math.** Differentiability of the actual Christoffel bilinear map at any
point of a boundaryless chart target. -/
theorem differentiableAt_chartChristoffelBilin_normed (g : RiemannianMetric I M)
    (a : M) (y : E) (hy : y ∈ (extChartAt I a).target) :
    DifferentiableAt ℝ (chartChristoffelBilin g a) y := by
  have hi : y ∈ interior (extChartAt I a).target :=
    (isOpen_extChartAt_target (I := I) a).interior_eq.symm ▸ hy
  exact ((contDiffOn_chartChristoffelBilin_normed g a).contDiffAt
    (isOpen_interior.mem_nhds hi)).differentiableAt (by norm_num)

/-- **Math.** Differentiate the actual Christoffel map along a coordinate line,
then evaluate on two constant tangent-coordinate vectors. -/
theorem chartChristoffelBilin_line_hasDerivAt (g : RiemannianMetric I M)
    (a : M) (y x u v : E) (hy : y ∈ (extChartAt I a).target) :
    HasDerivAt (fun r : ℝ => chartChristoffelBilin g a (y + r • x) u v)
      (fderiv ℝ (chartChristoffelBilin g a) y x u v) 0 := by
  have hline : HasDerivAt (fun r : ℝ => y + r • x) x 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const x).const_add y
  have hG := (differentiableAt_chartChristoffelBilin_normed g a y hy).hasFDerivAt
  have hGline : HasDerivAt (fun r : ℝ => chartChristoffelBilin g a (y + r • x))
      (fderiv ℝ (chartChristoffelBilin g a) y x) 0 := by
    have hg : HasFDerivAt (chartChristoffelBilin g a) (fderiv ℝ (chartChristoffelBilin g a) y)
        ((fun r : ℝ => y + r • x) 0) := by simpa only [zero_smul, add_zero] using hG
    exact HasFDerivAt.comp_hasDerivAt (l := chartChristoffelBilin g a)
      (l' := fderiv ℝ (chartChristoffelBilin g a) y)
      (f := fun r : ℝ => y + r • x) (f' := x) (0 : ℝ) hg hline
  have hh := (hGline.clm_apply (hasDerivAt_const 0 u)).clm_apply (hasDerivAt_const 0 v)
  simpa only [zero_smul, add_zero, map_zero] using hh

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [J.Boundaryless]

/-- **Math.** Splitting of the actual bilinear Christoffel map. -/
theorem chartChristoffelBilin_product (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y u v : E × F) (hy : y ∈ (extChartAt (I.prod J) a).target) :
    chartChristoffelBilin (productMetric g h) a y u v =
      (chartChristoffelBilin g a.1 y.1 u.1 v.1, chartChristoffelBilin h a.2 y.2 u.2 v.2) := by
  simp only [chartChristoffelBilin_apply_normed]
  exact chartChristoffelContraction_product g h a y u v hy

/-- **Math.** Derivative splitting follows by differentiating the actual
Christoffel identity on the open product-chart target. -/
theorem fderiv_chartChristoffelBilin_product
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u v : E × F) (hy : y ∈ (extChartAt (I.prod J) a).target) :
    fderiv ℝ (chartChristoffelBilin (productMetric g h) a) y x u v =
      (fderiv ℝ (chartChristoffelBilin g a.1) y.1 x.1 u.1 v.1,
       fderiv ℝ (chartChristoffelBilin h a.2) y.2 x.2 u.2 v.2) := by
  have hy' : y.1 ∈ (extChartAt I a.1).target ∧ y.2 ∈ (extChartAt J a.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using hy
  have hd := chartChristoffelBilin_line_hasDerivAt (productMetric g h) a y x u v hy
  have hd1 := chartChristoffelBilin_line_hasDerivAt g a.1 y.1 x.1 u.1 v.1 hy'.1
  have hd2 := chartChristoffelBilin_line_hasDerivAt h a.2 y.2 x.2 u.2 v.2 hy'.2
  have hline : ContinuousAt (fun r : ℝ => y + r • x) 0 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in nhds 0, y + r • x ∈ (extChartAt (I.prod J) a).target :=
    hline.eventually ((isOpen_extChartAt_target a).mem_nhds (by simpa using hy))
  have heq : (fun r : ℝ => chartChristoffelBilin (productMetric g h) a (y + r • x) u v) =ᶠ[nhds 0]
      (fun r : ℝ => (chartChristoffelBilin g a.1 (y.1 + r • x.1) u.1 v.1,
        chartChristoffelBilin h a.2 (y.2 + r • x.2) u.2 v.2)) := by
    filter_upwards [hnear] with r hr
    exact chartChristoffelBilin_product g h a (y + r • x) u v hr
  exact hd.unique ((hd1.prodMk hd2).congr_of_eventuallyEq heq)

/-- **Math.** Actual product chart Riemann curvature splits into the two factor
curvatures. All Christoffel and derivative splitting terms have been proved. -/
theorem chartCurvature_product (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u v : E × F) (hy : y ∈ (extChartAt (I.prod J) a).target) :
    chartCurvature (productMetric g h) a y x u v =
      (chartCurvature g a.1 y.1 x.1 u.1 v.1,
       chartCurvature h a.2 y.2 x.2 u.2 v.2) := by
  unfold chartCurvature christoffelCurvature
  simp only [fderiv_chartChristoffelBilin_product g h a y _ _ _ hy,
    chartChristoffelBilin_product g h a y _ _ hy]
  rfl

end CurveControl.Geometry

#print axioms CurveControl.Geometry.chartChristoffelBilin_apply_normed
#print axioms CurveControl.Geometry.contDiffOn_chartChristoffelBilin_normed
#print axioms CurveControl.Geometry.differentiableAt_chartChristoffelBilin_normed
#print axioms CurveControl.Geometry.chartChristoffelBilin_product
#print axioms CurveControl.Geometry.chartChristoffelBilin_line_hasDerivAt
#print axioms CurveControl.Geometry.fderiv_chartChristoffelBilin_product
#print axioms CurveControl.Geometry.chartCurvature_product
