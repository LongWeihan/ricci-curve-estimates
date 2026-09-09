import CurveControl.Geometry.ProductMetric
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-!
# Product chart connection splitting

The actual tangent coordinate change and inverse trivialization split on a
product chart. Hence the genuine chart Gram form of `productMetric` splits.
Differentiating that identity along coordinate lines proves metric compatibility
of the factorwise Christoffel candidate. Its symmetry and a pointwise Koszul
uniqueness argument identify it with the product metric's actual Christoffel
contraction throughout the chart target. No connection-splitting assumption is
used. Models need only be finite-dimensional normed spaces: the max-norm product
does not carry a spurious inner-product-space instance. Identification with a
canonical intrinsic LC connection on an L²-remodelled manifold is separate.
-/

open Set Riemannian Riemannian.Geodesic
open scoped ContDiff Manifold Topology

noncomputable section

namespace CurveControl.Geometry

/-- **Math.** Pointwise uniqueness of a symmetric connection coefficient with
a fixed metric-compatibility identity. This is the algebraic Koszul argument,
independent of any preferred basis or Hilbert norm on the chart model. -/
theorem connectionCoefficient_unique {V : Type*}
    (G : V → V → ℝ) (A B : V → V → V)
    (hGsym : ∀ u v, G u v = G v u)
    (hGsep : ∀ u v, (∀ w, G u w = G v w) → u = v)
    (hAsym : ∀ u v, A u v = A v u) (hBsym : ∀ u v, B u v = B v u)
    (hbalance : ∀ u v w, G (A u v) w + G v (A u w) =
      G (B u v) w + G v (B u w)) : A = B := by
  funext u v
  apply hGsep
  intro w
  have h1 := hbalance u v w
  have h2 := hbalance v u w
  have h3 := hbalance w u v
  rw [hGsym v (A u w), hGsym v (B u w)] at h1
  rw [hAsym v u, hBsym v u, hGsym u (A v w), hGsym u (B v w)] at h2
  rw [hAsym w u, hBsym w u, hAsym w v, hBsym w v,
    hGsym u (A v w), hGsym u (B v w)] at h3
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless]

/-- **Math.** Actual tangent-coordinate changes of the product manifold split. -/
theorem tangentCoordChange_product (a b p : M × N)
    (ha : p ∈ (extChartAt (I.prod J) a).source)
    (hb : p ∈ (extChartAt (I.prod J) b).source) :
    tangentCoordChange (I.prod J) a b p =
      (tangentCoordChange I a.1 b.1 p.1).prodMap (tangentCoordChange J a.2 b.2 p.2) := by
  have ha' : p.1 ∈ (extChartAt I a.1).source ∧ p.2 ∈ (extChartAt J a.2).source := by
    simpa only [extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod] using ha
  have hb' : p.1 ∈ (extChartAt I b.1).source ∧ p.2 ∈ (extChartAt J b.2).source := by
    simpa only [extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod] using hb
  have h1 : HasFDerivAt (extChartAt I b.1 ∘ (extChartAt I a.1).symm)
      (tangentCoordChange I a.1 b.1 p.1) (extChartAt I a.1 p.1) := by
    simpa only [I.range_eq_univ, hasFDerivWithinAt_univ] using
      hasFDerivWithinAt_tangentCoordChange (I := I) ⟨ha'.1, hb'.1⟩
  have h2 : HasFDerivAt (extChartAt J b.2 ∘ (extChartAt J a.2).symm)
      (tangentCoordChange J a.2 b.2 p.2) (extChartAt J a.2 p.2) := by
    simpa only [J.range_eq_univ, hasFDerivWithinAt_univ] using
      hasFDerivWithinAt_tangentCoordChange (I := J) ⟨ha'.2, hb'.2⟩
  rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  convert (HasFDerivAt.prodMap (extChartAt I a.1 p.1, extChartAt J a.2 p.2) h1 h2).fderiv using 1
  simp only [extChartAt_prod, PartialEquiv.prod_coe_symm, PartialEquiv.prod_coe,
    Function.comp_def]
  rfl

/-- **Math.** The inverse tangent-bundle trivialization of the actual product
chart acts separately on the two tangent components. -/
theorem trivializationAt_symm_product (a p : M × N)
    (hp : p ∈ (chartAt (ModelProd H K) a).source) (u : E × F) :
    (trivializationAt (E × F) (TangentSpace (I.prod J)) a).symm p u =
      ((trivializationAt E (TangentSpace I) a.1).symm p.1 u.1,
       (trivializationAt F (TangentSpace J) a.2).symm p.2 u.2) := by
  have hp' : p.1 ∈ (chartAt H a.1).source ∧ p.2 ∈ (chartAt K a.2).source := hp
  rw [trivializationAt_symm_eq_tangentCoordChange a hp,
    tangentCoordChange_product a p p (by rwa [extChartAt_source]) (mem_extChartAt_source p),
    trivializationAt_symm_eq_tangentCoordChange a.1 hp'.1,
    trivializationAt_symm_eq_tangentCoordChange a.2 hp'.2]
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Math.** Metric compatibility along a straight coordinate line, without an
inner-product-space instance on the chart model. -/
theorem chartMetricInner_line_hasDerivAt (g : RiemannianMetric I M) (a : M)
    (y x u v : E) (hy : y ∈ (extChartAt I a).target) :
    HasDerivAt (fun r : ℝ => chartMetricInner g a (y + r • x) u v)
      (chartMetricInner g a y (chartChristoffelContraction g a x u y) v +
       chartMetricInner g a y u (chartChristoffelContraction g a x v y)) 0 := by
  have hline : HasDerivAt (fun r : ℝ => y + r • x) x 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const x).const_add y
  have hbase : (extChartAt I a).symm y ∈
      (trivializationAt E (TangentSpace I) a).baseSet := by
    simpa only [extChartAt_source, TangentBundle.trivializationAt_baseSet] using (extChartAt I a).map_target hy
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE g a i j) y := by
    intro i j
    exact ((chartGramOnE_contDiffOn g a i j).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hy)).differentiableAt (by norm_num)
  have hd := hasDerivAt_chartMetricInner_along g a (fun r => y + r • x)
    (fun _ => u) (fun _ => v) hline.differentiableAt (differentiableAt_const u)
    (differentiableAt_const v) (by simpa using hG) (by simpa using hbase)
  simpa only [zero_smul, add_zero, covariantDerivCoord, hline.deriv,
    deriv_const, zero_add] using hd

/-- **Math.** The chart Gram form of the product metric splits, with vectors
read through the genuine chart trivializations. -/
theorem chartMetricInner_product (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a p : M × N) (hp : p ∈ (chartAt (ModelProd H K) a).source) (u v : E × F) :
    chartMetricInner (productMetric g h) a (extChartAt (I.prod J) a p) u v =
      chartMetricInner g a.1 (extChartAt I a.1 p.1) u.1 v.1 +
        chartMetricInner h a.2 (extChartAt J a.2 p.2) u.2 v.2 := by
  have hp' : p.1 ∈ (chartAt H a.1).source ∧ p.2 ∈ (chartAt K a.2).source := hp
  rw [chartMetricInner_extChartAt_eq_metricInner _ _ hp,
    trivializationAt_symm_product a p hp u, trivializationAt_symm_product a p hp v,
    productMetric_inner,
    chartMetricInner_extChartAt_eq_metricInner _ _ hp'.1,
    chartMetricInner_extChartAt_eq_metricInner _ _ hp'.2]

/-- **Math.** The product chart metric splitting at every point of its target. -/
theorem chartMetricInner_product_target (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y u v : E × F) (hy : y ∈ (extChartAt (I.prod J) a).target) :
    chartMetricInner (productMetric g h) a y u v =
      chartMetricInner g a.1 y.1 u.1 v.1 + chartMetricInner h a.2 y.2 u.2 v.2 := by
  have hp : (extChartAt (I.prod J) a).symm y ∈ (chartAt (ModelProd H K) a).source := by
    simpa only [extChartAt_source] using (extChartAt (I.prod J) a).map_target hy
  have he := chartMetricInner_product g h a ((extChartAt (I.prod J) a).symm y) hp u v
  rw [(extChartAt (I.prod J) a).right_inv hy] at he
  have hy' : y.1 ∈ (extChartAt I a.1).target ∧ y.2 ∈ (extChartAt J a.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using hy
  simpa only [extChartAt_prod, PartialEquiv.prod_coe_symm, Prod.map_fst, Prod.map_snd,
    (extChartAt I a.1).right_inv hy'.1, (extChartAt J a.2).right_inv hy'.2] using he

omit [I.Boundaryless] in
/-- **Math.** Nondegeneracy of the actual chart Gram form, transported through
the invertible tangent-coordinate change. -/
theorem chartMetricInner_separates (g : RiemannianMetric I M) (a : M)
    (y : E) (hy : y ∈ (extChartAt I a).target) (u v : E)
    (huv : ∀ w, chartMetricInner g a y u w = chartMetricInner g a y v w) : u = v := by
  let p := (extChartAt I a).symm y
  have hp : p ∈ (extChartAt I a).source := (extChartAt I a).map_target hy
  have hpc : p ∈ (chartAt H a).source := by simpa only [extChartAt_source] using hp
  have hpp := mem_extChartAt_source (I := I) p
  have hread : ∀ z w, chartMetricInner g a y z w =
      g.metricInner p (tangentCoordChange I a p p z) (tangentCoordChange I a p p w) := by
    intro z w
    rw [← (extChartAt I a).right_inv hy]
    rw [chartMetricInner_extChartAt_eq_metricInner _ _ hpc,
      trivializationAt_symm_eq_tangentCoordChange a hpc,
      trivializationAt_symm_eq_tangentCoordChange a hpc]
  have hTv : tangentCoordChange I a p p u = tangentCoordChange I a p p v := by
    apply (g.metricInner_eq_iff_eq p _ _).mp
    intro z
    have hh := huv (tangentCoordChange I p a p z)
    simp only [hread] at hh
    rw [tangentCoordChange_comp (I := I) ⟨⟨hpp, hp⟩, hpp⟩,
      tangentCoordChange_self (I := I) hpp] at hh
    exact hh
  have hh := congrArg (tangentCoordChange I p a p) hTv
  rw [tangentCoordChange_comp (I := I) ⟨⟨hp, hpp⟩, hp⟩,
    tangentCoordChange_comp (I := I) ⟨⟨hp, hpp⟩, hp⟩,
    tangentCoordChange_self (I := I) hp, tangentCoordChange_self (I := I) hp] at hh
  exact hh

/-- **Math.** Differentiating the genuine product chart metric splitting shows
that the two factor Christoffel corrections obey the product metric identity. -/
theorem product_connection_metric_balance
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u v : E × F) (hy : y ∈ (extChartAt (I.prod J) a).target) :
    chartMetricInner (productMetric g h) a y
        (chartChristoffelContraction (productMetric g h) a x u y) v +
      chartMetricInner (productMetric g h) a y u
        (chartChristoffelContraction (productMetric g h) a x v y) =
    chartMetricInner (productMetric g h) a y
        (chartChristoffelContraction g a.1 x.1 u.1 y.1,
         chartChristoffelContraction h a.2 x.2 u.2 y.2) v +
      chartMetricInner (productMetric g h) a y u
        (chartChristoffelContraction g a.1 x.1 v.1 y.1,
         chartChristoffelContraction h a.2 x.2 v.2 y.2) := by
  have hy' : y.1 ∈ (extChartAt I a.1).target ∧ y.2 ∈ (extChartAt J a.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using hy
  have hd := chartMetricInner_line_hasDerivAt (productMetric g h) a y x u v hy
  have hd1 := chartMetricInner_line_hasDerivAt g a.1 y.1 x.1 u.1 v.1 hy'.1
  have hd2 := chartMetricInner_line_hasDerivAt h a.2 y.2 x.2 u.2 v.2 hy'.2
  have hline : ContinuousAt (fun r : ℝ => y + r • x) 0 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in nhds 0, y + r • x ∈ (extChartAt (I.prod J) a).target :=
    hline.eventually ((isOpen_extChartAt_target a).mem_nhds (by simpa using hy))
  have heq : (fun r : ℝ => chartMetricInner (productMetric g h) a (y + r • x) u v) =ᶠ[nhds 0]
      (fun r : ℝ => chartMetricInner g a.1 (y.1 + r • x.1) u.1 v.1 +
        chartMetricInner h a.2 (y.2 + r • x.2) u.2 v.2) := by
    filter_upwards [hnear] with r hr
    exact chartMetricInner_product_target g h a (y + r • x) u v hr
  have he := hd.unique ((hd1.add hd2).congr_of_eventuallyEq heq)
  conv_rhs => rw [chartMetricInner_product_target g h a y _ _ hy,
    chartMetricInner_product_target g h a y _ _ hy]
  dsimp only at he ⊢
  linarith

/-- **Math.** Actual chart Christoffel coefficients of the product metric split
on the product chart target. This is derived from the differentiated metric and
torsion-free symmetry; no connection-splitting hypothesis is used. -/
theorem chartChristoffelContraction_product
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (a : M × N) (y x u : E × F) (hy : y ∈ (extChartAt (I.prod J) a).target) :
    chartChristoffelContraction (productMetric g h) a x u y =
      (chartChristoffelContraction g a.1 x.1 u.1 y.1,
       chartChristoffelContraction h a.2 x.2 u.2 y.2) := by
  have hsym : ∀ v w, chartMetricInner (productMetric g h) a y v w =
      chartMetricInner (productMetric g h) a y w v := by
    intro v w
    unfold chartMetricInner
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [chartGramOnE_symm (productMetric g h) a j i]
    ring
  have hh := connectionCoefficient_unique
    (chartMetricInner (productMetric g h) a y)
    (fun v w => chartChristoffelContraction (productMetric g h) a v w y)
    (fun v w => (chartChristoffelContraction g a.1 v.1 w.1 y.1,
      chartChristoffelContraction h a.2 v.2 w.2 y.2)) hsym
    (chartMetricInner_separates (productMetric g h) a y hy)
    (fun v w => chartChristoffelContraction_symm (productMetric g h) a v w y)
    (fun v w => Prod.ext (chartChristoffelContraction_symm g a.1 v.1 w.1 y.1)
      (chartChristoffelContraction_symm h a.2 v.2 w.2 y.2))
    (fun v w z => product_connection_metric_balance g h a y v w z hy)
  exact congrFun (congrFun hh x) u

end CurveControl.Geometry

#print axioms CurveControl.Geometry.tangentCoordChange_product
#print axioms CurveControl.Geometry.connectionCoefficient_unique
#print axioms CurveControl.Geometry.trivializationAt_symm_product
#print axioms CurveControl.Geometry.chartMetricInner_line_hasDerivAt
#print axioms CurveControl.Geometry.chartMetricInner_product
#print axioms CurveControl.Geometry.chartMetricInner_product_target
#print axioms CurveControl.Geometry.chartMetricInner_separates
#print axioms CurveControl.Geometry.product_connection_metric_balance
#print axioms CurveControl.Geometry.chartChristoffelContraction_product
