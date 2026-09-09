import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution
import MorganTianLib.Ch01.ChartCurvature

/-!
# Actual time variation of the Levi-Civita connection under Ricci flow

All time derivatives below hold the spatial chart and coordinate point fixed.
The connection variation is derived from the metric Ricci-flow equation using
upstream metric differentiation, rather than supplied as an extra hypothesis.
-/
open scoped ContDiff Manifold Topology Bundle
open Set Filter Riemannian Riemannian.Tensor Riemannian.Geodesic MorganTianLib
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
namespace CurveControl.Geometry.RicciConnectionVariation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] E) := NormedSpace.toIsBoundedSMul

/-- **Math.** The explicit raised covariant-Ricci expression for a connection coefficient. -/
def ricciVariationCoef (g : Riemannian.RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  - ∑ l, chartInvGramOnE (I := I) g α k l y *
    (chartCovRicciOnE (I := I) g α i l j y +
      chartCovRicciOnE (I := I) g α j l i y -
      chartCovRicciOnE (I := I) g α l i j y)

/-- **Math.** A genuine fixed-chart Christoffel time derivative under Ricci flow. -/
theorem hasDerivAt_chartChristoffel_ricci
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsRicciFlowOn g J) (α : M) (i j k : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivAt (fun s => chartChristoffel (I := I) (g s) α i j k y)
      (ricciVariationCoef (g t) α i j k y) t := by
  have h := MorganTianLib.hasDerivAt_chartChristoffel hg.smooth
    (isMetricVariationOn_of_isRicciFlowOn hg) α i j k ht hy
  rw [chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci g t α i j k hy] at h
  exact h

/-- **Math.** Fixed elementary bilinear maps used to reconstruct connection coefficients. -/
def coordinateBilin (i j k : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] E :=
  (chartCoordFunctional (E := E) i).smulRight
    ((chartCoordFunctional (E := E) j).smulRight (Module.finBasis ℝ E k))

/-- **Math.** The bilinear connection-variation tensor in this fixed chart. -/
def ricciVariationBilin (g : Riemannian.RiemannianMetric I M) (α : M) (y : E) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i, ∑ j, ∑ k, ricciVariationCoef g α i j k y • coordinateBilin (E := E) i j k

private theorem chartChristoffelBilin_eq_sum (g : Riemannian.RiemannianMetric I M)
    (α : M) (y : E) :
    MorganTianLib.chartChristoffelBilin (I := I) g α y =
      ∑ i, ∑ j, ∑ k, chartChristoffel (I := I) g α i j k y • coordinateBilin (E := E) i j k := by
  ext U V
  simp only [MorganTianLib.chartChristoffelBilin, coordinateBilin,
    sum_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_smul]
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  funext k
  congr 1
  ring

/-- **Math.** The true Levi-Civita coefficient CLM is jointly smooth in time
and fixed-chart coordinates on the interior time domain. -/
theorem contDiffOn_chartChristoffelBilin_timeSpace
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartChristoffelBilin (I := I) (g z.1) α z.2)
      (interior J ×ˢ (extChartAt I α).target) := by
  simp_rw [chartChristoffelBilin_eq_sum]
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
    (contDiffOn_chartChristoffel_timeSpace hg α i j k).smul contDiffOn_const

/-- **Math.** Joint smoothness at a legal interior time and chart point. -/
theorem contDiffAt_chartChristoffelBilin_timeSpace
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartChristoffelBilin (I := I) (g z.1) α z.2) (t, y) :=
  (contDiffOn_chartChristoffelBilin_timeSpace hg α).contDiffAt
    ((isOpen_interior.prod (isOpen_extChartAt_target (I := I) α)).mem_nhds ⟨ht, hy⟩)

/-- **Math.** The joint C² interface for the curvature commutation calculation. -/
theorem contDiffAt_two_chartChristoffelBilin_timeSpace
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    ContDiffAt ℝ 2
      (fun z : ℝ × E => MorganTianLib.chartChristoffelBilin (I := I) (g z.1) α z.2) (t, y) :=
  (contDiffAt_chartChristoffelBilin_timeSpace hg α ht hy).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

/-- **Math.** The actual bilinear CLM, not just its scalar coefficients, has this derivative. -/
theorem hasDerivAt_chartChristoffelBilin_ricci
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsRicciFlowOn g J) (α : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivAt (fun s => MorganTianLib.chartChristoffelBilin (I := I) (g s) α y)
      (ricciVariationBilin (g t) α y) t := by
  simp_rw [chartChristoffelBilin_eq_sum]
  unfold ricciVariationBilin
  exact
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_chartChristoffel_ricci hg α i j k ht hy).smul_const
        (coordinateBilin (E := E) i j k))

/-- **Math.** Identification with Lean's actual time-slice derivative of the connection CLM. -/
theorem deriv_chartChristoffelBilin_ricci
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsRicciFlowOn g J) (α : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    deriv (fun s => MorganTianLib.chartChristoffelBilin (I := I) (g s) α y) t =
      ricciVariationBilin (g t) α y :=
  (hasDerivAt_chartChristoffelBilin_ricci (E := E) (I := I) hg α ht hy).deriv

/-- **Math.** Evaluation of the CLM derivative on two fixed spatial vectors. -/
theorem hasDerivAt_chartChristoffelContraction_ricci
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsRicciFlowOn g J) (α : M) (U V : E)
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivAt (fun s => chartChristoffelContraction (I := I) (g s) α U V y)
      (ricciVariationBilin (g t) α y U V) t := by
  have h := ((hasDerivAt_chartChristoffelBilin_ricci (E := E) (I := I) hg α ht hy).clm_apply
    (hasDerivAt_const t U)).clm_apply (hasDerivAt_const t V)
  simpa only [zero_add, map_zero, add_zero, MorganTianLib.chartChristoffelBilin_apply] using h

/-- **Math.** Evaluation of the actual variation CLM on chart-basis vectors. -/
theorem ricciVariationBilin_basis (g : Riemannian.RiemannianMetric I M)
    (α : M) (y : E) (i j : Fin (Module.finrank ℝ E)) :
    ricciVariationBilin (I := I) g α y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) =
      ∑ k, ricciVariationCoef g α i j k y • Module.finBasis ℝ E k := by
  classical
  simp [ricciVariationBilin, coordinateBilin, chartCoordFunctional_apply,
    chartCoord_def, Module.Basis.repr_self, Finsupp.single_apply]

/-- **Math.** Lowering the genuinely derived connection variation cancels the inverse metric. -/
theorem ricciVariationCoef_lower
    (g : Riemannian.RiemannianMetric I M) (α : M)
    (i j a : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    (∑ k, chartGramOnE (I := I) g α a k y * ricciVariationCoef g α i j k y) =
      -chartCovRicciOnE (I := I) g α i a j y
      -chartCovRicciOnE (I := I) g α j a i y
      +chartCovRicciOnE (I := I) g α a i j y := by
  classical
  have hp : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change (extChartAt I α).symm y ∈ (chartAt H α).source
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I α]
    exact (extChartAt I α).map_target hy
  have hinv (l : Fin (Module.finrank ℝ E)) :
      (∑ k, chartGramOnE (I := I) g α a k y * chartInvGramOnE (I := I) g α k l y)
        = if a = l then (1 : ℝ) else 0 := by
    change (chartGramMatrix (I := I) g α ((extChartAt I α).symm y) *
      chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y)) a l = _
    rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hp, Matrix.one_apply]
  unfold ricciVariationCoef
  simp_rw [mul_neg, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hinv]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

private theorem linear_eq_of_finBasis {F G : E → ℝ}
    (hFa : ∀ x y, F (x + y) = F x + F y)
    (hFs : ∀ (c : ℝ) x, F (c • x) = c * F x)
    (hGa : ∀ x y, G (x + y) = G x + G y)
    (hGs : ∀ (c : ℝ) x, G (c • x) = c * G x)
    (h : ∀ i, F (Module.finBasis ℝ E i) = G (Module.finBasis ℝ E i)) (x : E) : F x = G x := by
  let f : E →ₗ[ℝ] ℝ := ⟨⟨F, hFa⟩, hFs⟩
  let g : E →ₗ[ℝ] ℝ := ⟨⟨G, hGa⟩, hGs⟩
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => L x) ((Module.finBasis ℝ E).ext h : f = g)

/-- **Math.** Metric lowering of the true CLM variation on a chart basis. -/
theorem ricciVariationBilin_lower_basis
    (g : Riemannian.RiemannianMetric I M) (α : M)
    (i j a : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    let p := (extChartAt I α).symm y
    g.metricInner p
      ((trivializationAt E (TangentSpace I) α).symm p
        (ricciVariationBilin (I := I) g α y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)))
      (chartBasisVecFiber (I := I) α a p) =
      -chartCovRicciOnE (I := I) g α i j a y
      -chartCovRicciOnE (I := I) g α j i a y
      +chartCovRicciOnE (I := I) g α a i j y := by
  classical
  dsimp only
  have hp : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I α]
    exact (extChartAt I α).map_target hy
  rw [ricciVariationBilin_basis]
  rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hp, map_sum]
  simp only [map_smul]
  rw [Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hp]
  change g.metricInner _ (∑ k, ricciVariationCoef g α i j k y •
    chartBasisVecFiber (I := I) α k _) (chartBasisVecFiber (I := I) α a _) = _
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℝ E))),
      g.metricInner ((extChartAt I α).symm y)
        (∑ k ∈ s, ricciVariationCoef g α i j k y •
          chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α a ((extChartAt I α).symm y)) =
      ∑ k ∈ s, ricciVariationCoef g α i j k y * chartGramOnE (I := I) g α k a y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact g.metricInner_zero_left _ _
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, g.metricInner_add_left,
        g.metricInner_smul_left, ih]
      rfl
  rw [hsum]
  simp_rw [chartGramOnE_symm (I := I) g α _ a, mul_comm]
  rw [ricciVariationCoef_lower g α i j a hy,
    chartCovRicciOnE_symm g α i a j hy, chartCovRicciOnE_symm g α j a i hy]

/-- **Math.** The time-slice derivative, lowered in coordinates, equals the intrinsic
covariant derivative of Ricci on the three actual chart-frame tangent vectors. -/
theorem deriv_chartChristoffel_lower_intrinsic
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsRicciFlowOn g J) (α : M) (i j a : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    let p := (extChartAt I α).symm y
    let b := fun k => chartBasisVecFiber (I := I) α k p
    let hLC := (g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
      (fun X Y W q => (g t).koszulDualSection_dual X Y W q)
    (∑ k, chartGramOnE (I := I) (g t) α a k y *
      deriv (fun s => chartChristoffel (I := I) (g s) α i j k y) t) =
      -covRicciAt (g t) (g t).leviCivitaConnection hLC p (b i) (b j) (b a)
      -covRicciAt (g t) (g t).leviCivitaConnection hLC p (b j) (b i) (b a)
      +covRicciAt (g t) (g t).leviCivitaConnection hLC p (b a) (b i) (b j) := by
  dsimp only
  simp_rw [(hasDerivAt_chartChristoffel_ricci hg α _ _ _ ht hy).deriv]
  rw [ricciVariationCoef_lower (g t) α i j a hy]
  rw [chartCovRicciOnE_symm (g t) α i a j hy,
    chartCovRicciOnE_symm (g t) α j a i hy]
  simp_rw [chartCovRicciOnE_eq_covRicciAt_chartBasis (g t) α _ _ _ hy]

/-- **Math.** Arbitrary-vector intrinsic metric lowering of the actual time derivative of
Levi-Civita's bilinear coefficient field, using the fixed chart readback. -/
theorem deriv_chartChristoffelBilin_lower_intrinsic
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsRicciFlowOn g J) (α : M) (U V W : E)
    {t : ℝ} (ht : t ∈ interior J) {y : E} (hy : y ∈ (extChartAt I α).target) :
    let p := (extChartAt I α).symm y
    let R := (trivializationAt E (TangentSpace I) α).symm p
    let A := deriv (fun s => MorganTianLib.chartChristoffelBilin (I := I) (g s) α y) t
    let hLC := (g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
      (fun X Y W q => (g t).koszulDualSection_dual X Y W q)
    (g t).metricInner p (R (A U V)) (R W) =
      -covRicciAt (g t) (g t).leviCivitaConnection hLC p (R U) (R V) (R W)
      -covRicciAt (g t) (g t).leviCivitaConnection hLC p (R V) (R U) (R W)
      +covRicciAt (g t) (g t).leviCivitaConnection hLC p (R W) (R U) (R V) := by
  classical
  dsimp only
  rw [deriv_chartChristoffelBilin_ricci hg α ht hy]
  have hp : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I α]
    exact (extChartAt I α).map_target hy
  simp_rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hp]
  let p := (extChartAt I α).symm y
  let R := Bundle.Trivialization.symmₗ ℝ (trivializationAt E (TangentSpace I) α) p
  let hLC := (g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
    (fun X Y W q => (g t).koszulDualSection_dual X Y W q)
  let L := fun u v w : E => (g t).metricInner p (R (ricciVariationBilin (g t) α y u v)) (R w)
  let Q := fun u v w : E =>
    -covRicciAt (g t) (g t).leviCivitaConnection hLC p (R u) (R v) (R w)
    -covRicciAt (g t) (g t).leviCivitaConnection hLC p (R v) (R u) (R w)
    +covRicciAt (g t) (g t).leviCivitaConnection hLC p (R w) (R u) (R v)
  change L U V W = Q U V W
  refine linear_eq_of_finBasis (F := fun u => L u V W) (G := fun u => Q u V W)
    (x := U) ?_ ?_ ?_ ?_ ?_
  · intros; dsimp only [L, Q]; simp only [map_add, add_apply, Riemannian.RiemannianMetric.metricInner_add_left]
  · intros; dsimp only [L, Q]; simp only [map_smul, smul_apply, Riemannian.RiemannianMetric.metricInner_smul_left]
  · intros; dsimp only [L, Q]; simp only [map_add, covRicciAt_add_dir, covRicciAt_add_fst]; ring
  · intros; dsimp only [L, Q]; simp only [map_smul, covRicciAt_smul_dir, covRicciAt_smul_fst]; ring
  · intro i
    refine linear_eq_of_finBasis (F := fun v => L (Module.finBasis ℝ E i) v W)
      (G := fun v => Q (Module.finBasis ℝ E i) v W) (x := V) ?_ ?_ ?_ ?_ ?_
    · intros; dsimp only [L, Q]; simp only [map_add, Riemannian.RiemannianMetric.metricInner_add_left]
    · intros; dsimp only [L, Q]; simp only [map_smul, Riemannian.RiemannianMetric.metricInner_smul_left]
    · intros; dsimp only [L, Q]; simp only [map_add, covRicciAt_add_dir, covRicciAt_add_fst, covRicciAt_add_snd]; ring
    · intros; dsimp only [L, Q]; simp only [map_smul, covRicciAt_smul_dir, covRicciAt_smul_fst, covRicciAt_smul_snd]; ring
    · intro j
      refine linear_eq_of_finBasis
        (F := fun w => L (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) w)
        (G := fun w => Q (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) w)
        (x := W) ?_ ?_ ?_ ?_ ?_
      · intros; dsimp only [L, Q]; simp only [map_add, Riemannian.RiemannianMetric.metricInner_add_right]
      · intros; dsimp only [L, Q]; simp only [map_smul, Riemannian.RiemannianMetric.metricInner_smul_right]
      · intros; dsimp only [L, Q]; simp only [map_add, covRicciAt_add_dir, covRicciAt_add_snd]; ring
      · intros; dsimp only [L, Q]; simp only [map_smul, covRicciAt_smul_dir, covRicciAt_smul_snd]; ring
      · intro a
        dsimp only [L, Q, R, p, hLC]
        simp_rw [Bundle.Trivialization.coe_symmₗ (R := ℝ)
          (trivializationAt E (TangentSpace I) α) hp]
        change (g t).metricInner _ _ (chartBasisVecFiber (I := I) α a _) = _
        rw [ricciVariationBilin_lower_basis (g t) α i j a hy]
        simp_rw [chartCovRicciOnE_eq_covRicciAt_chartBasis (g t) α _ _ _ hy]
        rfl

end CurveControl.Geometry.RicciConnectionVariation

#print axioms CurveControl.Geometry.RicciConnectionVariation.hasDerivAt_chartChristoffel_ricci
#print axioms CurveControl.Geometry.RicciConnectionVariation.hasDerivAt_chartChristoffelBilin_ricci
#print axioms CurveControl.Geometry.RicciConnectionVariation.hasDerivAt_chartChristoffelContraction_ricci

#print axioms CurveControl.Geometry.RicciConnectionVariation.deriv_chartChristoffelBilin_lower_intrinsic

#print axioms CurveControl.Geometry.RicciConnectionVariation.contDiffAt_chartChristoffelBilin_timeSpace
#print axioms CurveControl.Geometry.RicciConnectionVariation.contDiffAt_two_chartChristoffelBilin_timeSpace
