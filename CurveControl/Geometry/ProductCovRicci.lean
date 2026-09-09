import CurveControl.Geometry.ProductIntrinsicCurvature
import CurveControl.Geometry.ProductL2Connection
import CurveControl.Geometry.AmbientBounds

/-!
# Covariant Ricci derivatives of the genuine Hilbert-model product

The analytic layer differentiates the actual coefficient fields. Product
splitting hypotheses in auxiliary lemmas concern only the lower-order Ricci
and connection coefficients, never their covariant derivative.
-/
open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Topology ContDiff Manifold Bundle
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
namespace CurveControl.Geometry.ProductCovRicci

section Analytic
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Math.** The actual coordinate covariant derivative of a bilinear tensor. -/
def covBilinDerivative (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ) (y U V W : E) : ℝ :=
  fderiv ℝ A y U V W - A y (Γ y U V) W - A y V (Γ y U W)

/-- **Math.** Ordinary derivative of an actual bilinear coefficient field on a coordinate line. -/
theorem bilin_line_hasDerivAt {A : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (hA : DifferentiableAt ℝ A y) (U V W : E) :
    HasDerivAt (fun r : ℝ => A (y + r • U) V W) (fderiv ℝ A y U V W) 0 := by
  have hl : HasDerivAt (fun r : ℝ => y + r • U) U 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const U).const_add y
  have hAy : HasFDerivAt A (fderiv ℝ A y) (y + (0 : ℝ) • U) := by
    simpa only [zero_smul, add_zero] using hA.hasFDerivAt
  have h := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (l := A)
    (f := fun r : ℝ => y + r • U) 0 hAy hl
  have hh := (h.clm_apply (hasDerivAt_const (0 : ℝ) V)).clm_apply (hasDerivAt_const (0 : ℝ) W)
  simpa using hh

/-- **Math.** Differentiating the proved splitting of the bilinear coefficients
under a fixed linear change of model. -/
theorem fderiv_bilin_split (e : (E × F) ≃L[ℝ] G)
    {A : E → E →L[ℝ] E →L[ℝ] ℝ} {B : F → F →L[ℝ] F →L[ℝ] ℝ}
    {C : G → G →L[ℝ] G →L[ℝ] ℝ} {y : G}
    (hA : DifferentiableAt ℝ A (e.symm y).1)
    (hB : DifferentiableAt ℝ B (e.symm y).2) (hC : DifferentiableAt ℝ C y)
    (hsplit : ∀ᶠ z in 𝓝 y, ∀ V W,
      C z V W = A (e.symm z).1 (e.symm V).1 (e.symm W).1 +
        B (e.symm z).2 (e.symm V).2 (e.symm W).2) (U V W : G) :
    fderiv ℝ C y U V W =
      fderiv ℝ A (e.symm y).1 (e.symm U).1 (e.symm V).1 (e.symm W).1 +
      fderiv ℝ B (e.symm y).2 (e.symm U).2 (e.symm V).2 (e.symm W).2 := by
  have hd := bilin_line_hasDerivAt hC U V W
  have ha := bilin_line_hasDerivAt hA (e.symm U).1 (e.symm V).1 (e.symm W).1
  have hb := bilin_line_hasDerivAt hB (e.symm U).2 (e.symm V).2 (e.symm W).2
  have ht : Tendsto (fun r : ℝ => y + r • U) (𝓝 0) (𝓝 y) := by
    have hct : Continuous (fun r : ℝ => y + r • U) := by fun_prop
    simpa only [zero_smul, add_zero] using hct.continuousAt.tendsto (x := 0)
  have heq : (fun r : ℝ => C (y + r • U) V W) =ᶠ[𝓝 0]
      (fun r => A ((e.symm y).1 + r • (e.symm U).1) (e.symm V).1 (e.symm W).1 +
        B ((e.symm y).2 + r • (e.symm U).2) (e.symm V).2 (e.symm W).2) := by
    filter_upwards [ht.eventually hsplit] with r hr
    simpa only [map_add, map_smul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] using hr V W
  exact hd.unique ((ha.add hb).congr_of_eventuallyEq heq)

/-- **Math.** Covariant tensor differentiation commutes with the actual product
splitting, by the preceding derivative theorem and the connection correction terms. -/
theorem covBilinDerivative_split (e : (E × F) ≃L[ℝ] G)
    {ΓA : E → E →L[ℝ] E →L[ℝ] E} {ΓB : F → F →L[ℝ] F →L[ℝ] F}
    {ΓC : G → G →L[ℝ] G →L[ℝ] G}
    {A : E → E →L[ℝ] E →L[ℝ] ℝ} {B : F → F →L[ℝ] F →L[ℝ] ℝ}
    {C : G → G →L[ℝ] G →L[ℝ] ℝ} {y : G}
    (hA : DifferentiableAt ℝ A (e.symm y).1)
    (hB : DifferentiableAt ℝ B (e.symm y).2) (hC : DifferentiableAt ℝ C y)
    (hsplit : ∀ᶠ z in 𝓝 y, ∀ V W,
      C z V W = A (e.symm z).1 (e.symm V).1 (e.symm W).1 +
        B (e.symm z).2 (e.symm V).2 (e.symm W).2)
    (hΓ : ∀ U V, ΓC y U V = e
      (ΓA (e.symm y).1 (e.symm U).1 (e.symm V).1,
       ΓB (e.symm y).2 (e.symm U).2 (e.symm V).2)) (U V W : G) :
    covBilinDerivative ΓC C y U V W =
      covBilinDerivative ΓA A (e.symm y).1 (e.symm U).1 (e.symm V).1 (e.symm W).1 +
      covBilinDerivative ΓB B (e.symm y).2 (e.symm U).2 (e.symm V).2 (e.symm W).2 := by
  have hzero := hsplit.self_of_nhds
  unfold covBilinDerivative
  rw [fderiv_bilin_split e hA hB hC hsplit U V W, hzero, hzero, hΓ, hΓ]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  ring

end Analytic
section ActualRicci
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := NormedSpace.toIsBoundedSMul

/-- **Math.** A constant coordinate bilinear functional. -/
def coordinatePair (i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] ℝ :=
  (chartCoordFunctional (E := E) i).smulRight (chartCoordFunctional (E := E) j)

/-- **Math.** The genuine coordinate Ricci tensor as a continuously bilinear field. -/
def chartRicciBilin (g : Riemannian.RiemannianMetric I M) (α : M) (y : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ∑ j, chartRicciCoefOnE (I := I) g α i j y • coordinatePair i j

/-- **Math.** The packaged tensor has exactly the actual Ricci coefficients. -/
theorem chartRicciBilin_basis (g : Riemannian.RiemannianMetric I M) (α : M)
    (y : E) (i j : Fin (Module.finrank ℝ E)) :
    chartRicciBilin g α y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) =
      chartRicciCoefOnE (I := I) g α i j y := by
  classical
  simp [chartRicciBilin, coordinatePair, chartCoordFunctional_apply, chartCoord_def,
    Module.Basis.repr_self, Finsupp.single_apply]

/-- **Math.** Actual Ricci coefficients are smooth on every valid chart target. -/
theorem contDiffAt_chartRicciBilin (g : Riemannian.RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (chartRicciBilin g α) y := by
  unfold chartRicciBilin
  refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_
  have hcoef : ContDiffAt ℝ ∞ (fun z : E => chartRicciCoefOnE (I := I) g α i j z) y :=
    (chartRicciCoefOnE_contDiffOn g α i j).contDiffAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  exact hcoef.smul (contDiffAt_const (c := coordinatePair (E := E) i j))

private theorem linear_eq_of_finBasis {f g : E → ℝ}
    (hfadd : ∀ u v, f (u + v) = f u + f v) (hfsmul : ∀ c u, f (c • u) = c * f u)
    (hgadd : ∀ u v, g (u + v) = g u + g v) (hgsmul : ∀ c u, g (c • u) = c * g u)
    (hb : ∀ i, f (Module.finBasis ℝ E i) = g (Module.finBasis ℝ E i)) (u : E) : f u = g u := by
  let fL : E →ₗ[ℝ] ℝ := ⟨⟨f, hfadd⟩, hfsmul⟩
  let gL : E →ₗ[ℝ] ℝ := ⟨⟨g, hgadd⟩, hgsmul⟩
  have heq : fL = gL := (Module.finBasis ℝ E).ext hb
  exact DFunLike.congr_fun heq u

/-- **Math.** Arbitrary-vector identification with the actual intrinsic Ricci tensor. -/
theorem chartRicciBilin_eq_intrinsic (g : Riemannian.RiemannianMetric I M)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) (V W : E) :
    let p := (extChartAt I α).symm y
    let R := (trivializationAt E (TangentSpace I) α).symm p
    chartRicciBilin g α y V W = ricciTensorAt g p (R V) (R W) := by
  classical
  dsimp only
  have hp : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  simp_rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hp]
  let p := (extChartAt I α).symm y
  let R := Bundle.Trivialization.symmₗ ℝ (trivializationAt E (TangentSpace I) α) p
  apply linear_eq_of_finBasis (f := fun U => chartRicciBilin g α y U W)
    (g := fun U => ricciTensorAt g p (R U) (R W))
  · intros; simp only [map_add, add_apply]
  · intros; simp only [map_smul, smul_apply, smul_eq_mul]
  · intros; simp only [map_add, LinearMap.add_apply]
  · intros; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro i
    apply linear_eq_of_finBasis (f := fun U => chartRicciBilin g α y (Module.finBasis ℝ E i) U)
      (g := fun U => ricciTensorAt g p (R (Module.finBasis ℝ E i)) (R U))
    · intros; simp only [map_add]
    · intros; simp only [map_smul, smul_eq_mul]
    · intros; simp only [map_add]
    · intros; simp only [map_smul, smul_eq_mul]
    · intro j
      rw [chartRicciBilin_basis, chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g α i j hy]
      dsimp only [p, R]
      simp_rw [Bundle.Trivialization.coe_symmₗ (R := ℝ)
        (trivializationAt E (TangentSpace I) α) hp]
      rfl

/-- **Math.** Differentiating the actual Ricci field agrees with differentiating its coefficients. -/
theorem fderiv_chartRicciBilin_basis (g : Riemannian.RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) (r i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartRicciBilin g α) y (Module.finBasis ℝ E r)
      (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) =
      partialDeriv (E := E) r (chartRicciCoefOnE (I := I) g α i j) y := by
  have hA := (contDiffAt_chartRicciBilin g α hy).differentiableAt (by simp)
  have hd : HasFDerivAt (fun z => chartRicciBilin g α z (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
      (((fderiv ℝ (chartRicciBilin g α) y).flip (Module.finBasis ℝ E i)).flip (Module.finBasis ℝ E j)) y := by
    simpa using (hA.hasFDerivAt.clm_apply (hasFDerivAt_const (Module.finBasis ℝ E i) y)).clm_apply
      (hasFDerivAt_const (Module.finBasis ℝ E j) y)
  have heq : (fun z => chartRicciBilin g α z (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)) =
      chartRicciCoefOnE (I := I) g α i j := funext fun z => chartRicciBilin_basis g α z i j
  rw [heq] at hd
  exact (congrArg (fun L : E →L[ℝ] ℝ => L (Module.finBasis ℝ E r)) hd.fderiv).symm

/-- **Math.** The actual coordinate covariant derivative has the standard Ricci coefficients. -/
theorem covBilinDerivative_chartRicci_basis (g : Riemannian.RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) (r i j : Fin (Module.finrank ℝ E)) :
    covBilinDerivative (Riemannian.Jacobi.chartChristoffelBilin (I := I) g α)
      (chartRicciBilin g α) y (Module.finBasis ℝ E r) (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) =
      chartCovRicciOnE (I := I) g α r i j y := by
  unfold covBilinDerivative
  rw [fderiv_chartRicciBilin_basis g α hy,
    Riemannian.Jacobi.chartChristoffelBilin_basis,
    Riemannian.Jacobi.chartChristoffelBilin_basis]
  simp only [map_sum, sum_apply, map_smul, smul_apply,
    smul_eq_mul, chartRicciBilin_basis, chartCovRicciOnE]

/-- **Math.** Actual coordinate covariant differentiation equals intrinsic covRicci
on arbitrary vectors, obtained from the coefficient identity by trilinearity. -/
theorem covBilinDerivative_chartRicci_eq_intrinsic (g : Riemannian.RiemannianMetric I M)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) (U V W : E) :
    let p := (extChartAt I α).symm y
    let R := (trivializationAt E (TangentSpace I) α).symm p
    covBilinDerivative (Riemannian.Jacobi.chartChristoffelBilin (I := I) g α)
      (chartRicciBilin g α) y U V W = AmbientBounds.covRic g p (R U) (R V) (R W) := by
  classical
  dsimp only
  have hp : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  simp_rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hp]
  let p := (extChartAt I α).symm y
  let R := Bundle.Trivialization.symmₗ ℝ (trivializationAt E (TangentSpace I) α) p
  let L := covBilinDerivative (Riemannian.Jacobi.chartChristoffelBilin (I := I) g α) (chartRicciBilin g α) y
  let Q := fun u v w => AmbientBounds.covRic g p (R u) (R v) (R w)
  change L U V W = Q U V W
  apply linear_eq_of_finBasis (f := fun u => L u V W) (g := fun u => Q u V W)
  · intros; dsimp only [L, covBilinDerivative]; simp only [map_add, add_apply]; ring
  · intros; dsimp only [L, covBilinDerivative]; simp only [map_smul, smul_apply, smul_eq_mul]; ring
  · intros; dsimp only [Q, AmbientBounds.covRic]; simp only [map_add, covRicciAt_add_dir]
  · intros; dsimp only [Q, AmbientBounds.covRic]; simp only [map_smul, covRicciAt_smul_dir]
  · intro r
    apply linear_eq_of_finBasis (f := fun v => L (Module.finBasis ℝ E r) v W)
      (g := fun v => Q (Module.finBasis ℝ E r) v W)
    · intros; dsimp only [L, covBilinDerivative]; simp only [map_add, add_apply]; ring
    · intros; dsimp only [L, covBilinDerivative]; simp only [map_smul, smul_apply, smul_eq_mul]; ring
    · intros; dsimp only [Q, AmbientBounds.covRic]; simp only [map_add, covRicciAt_add_fst]
    · intros; dsimp only [Q, AmbientBounds.covRic]; simp only [map_smul, covRicciAt_smul_fst]
    · intro i
      apply linear_eq_of_finBasis (f := fun w => L (Module.finBasis ℝ E r) (Module.finBasis ℝ E i) w)
        (g := fun w => Q (Module.finBasis ℝ E r) (Module.finBasis ℝ E i) w)
      · intros; dsimp only [L, covBilinDerivative]; simp only [map_add]; ring
      · intros; dsimp only [L, covBilinDerivative]; simp only [map_smul, smul_eq_mul]; ring
      · intros; dsimp only [Q, AmbientBounds.covRic]; simp only [map_add, covRicciAt_add_snd]
      · intros; dsimp only [Q, AmbientBounds.covRic]; simp only [map_smul, covRicciAt_smul_snd]
      · intro j
        dsimp only [L, Q, p, R]
        simp_rw [Bundle.Trivialization.coe_symmₗ (R := ℝ)
          (trivializationAt E (TangentSpace I) α) hp]
        rw [covBilinDerivative_chartRicci_basis g α hy]
        exact chartCovRicciOnE_eq_covRicciAt_chartBasis g α r i j hy

end ActualRicci
section Product
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]

/-- **Math.** Inverse tangent coordinates in the Hilbert product split into factors. -/
theorem readback_productL2 (a p : M × N)
    (hp : p ∈ (chartAt (ModelProd H K) a).source) (u : WithLp 2 (E × F)) :
    productL2Equiv.symm ((trivializationAt (WithLp 2 (E × F))
      (TangentSpace (productL2Model I J)) a).symm p u) =
      ((trivializationAt E (TangentSpace I) a.1).symm p.1 (productL2Equiv.symm u).1,
       (trivializationAt F (TangentSpace J) a.2).symm p.2 (productL2Equiv.symm u).2) := by
  rw [trivializationAt_symm_eq_tangentCoordChange a hp,
    productL2_tangentCoordChange I J a p p
      ⟨by rwa [extChartAt_source], mem_extChartAt_source p⟩]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [← trivializationAt_symm_eq_tangentCoordChange a hp]
  exact trivializationAt_symm_product a p hp _

/-- **Math.** The actual Ricci coefficient field splits on every valid product chart. -/
theorem chartRicciBilin_productL2 (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (a : M × N) (y V W : WithLp 2 (E × F))
    (hy : y ∈ (extChartAt (productL2Model I J) a).target) :
    chartRicciBilin (productL2Metric I J g h) a y V W =
      chartRicciBilin g a.1 (productL2Equiv.symm y).1 (productL2Equiv.symm V).1 (productL2Equiv.symm W).1 +
      chartRicciBilin h a.2 (productL2Equiv.symm y).2 (productL2Equiv.symm V).2 (productL2Equiv.symm W).2 := by
  have hxy : (productL2Equiv.symm y).1 ∈ (extChartAt I a.1).target ∧
      (productL2Equiv.symm y).2 ∈ (extChartAt J a.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using
      productL2_target_inverse I J a y hy
  have hp : (extChartAt (productL2Model I J) a).symm y ∈
      (chartAt (ModelProd H K) a).source := by
    simpa only [extChartAt_source] using (extChartAt (productL2Model I J) a).map_target hy
  rw [chartRicciBilin_eq_intrinsic _ _ hy, chartRicciBilin_eq_intrinsic _ _ hxy.1,
    chartRicciBilin_eq_intrinsic _ _ hxy.2]
  rw [ricciTensorAt_productL2, readback_productL2 a _ hp V, readback_productL2 a _ hp W]
  rfl

/-- **Math.** Actual covariant Ricci derivatives split under the Hilbert product metric. -/
theorem covRic_productL2 (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) (U V W : TangentSpace (productL2Model I J) p) :
    AmbientBounds.covRic (productL2Metric I J g h) p U V W =
      AmbientBounds.covRic g p.1 (productL2Equiv.symm U).1 (productL2Equiv.symm V).1 (productL2Equiv.symm W).1 +
      AmbientBounds.covRic h p.2 (productL2Equiv.symm U).2 (productL2Equiv.symm V).2 (productL2Equiv.symm W).2 := by
  change WithLp 2 (E × F) at U V W
  let y := extChartAt (productL2Model I J) p p
  have hy : y ∈ (extChartAt (productL2Model I J) p).target := mem_extChartAt_target p
  have hxy : (productL2Equiv.symm y).1 ∈ (extChartAt I p.1).target ∧
      (productL2Equiv.symm y).2 ∈ (extChartAt J p.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, Set.mem_prod] using
      productL2_target_inverse I J p y hy
  have hsplit : ∀ᶠ z in 𝓝 y, ∀ v w,
      chartRicciBilin (productL2Metric I J g h) p z v w =
      chartRicciBilin g p.1 (productL2Equiv.symm z).1 (productL2Equiv.symm v).1 (productL2Equiv.symm w).1 +
      chartRicciBilin h p.2 (productL2Equiv.symm z).2 (productL2Equiv.symm v).2 (productL2Equiv.symm w).2 := by
    filter_upwards [(isOpen_extChartAt_target (I := productL2Model I J) p).mem_nhds hy] with z hz v w
    exact chartRicciBilin_productL2 g h p z v w hz
  have hΓ : ∀ u v, Riemannian.Jacobi.chartChristoffelBilin (productL2Metric I J g h) p y u v =
      productL2Equiv (Riemannian.Jacobi.chartChristoffelBilin g p.1 (productL2Equiv.symm y).1
        (productL2Equiv.symm u).1 (productL2Equiv.symm v).1,
      Riemannian.Jacobi.chartChristoffelBilin h p.2 (productL2Equiv.symm y).2
        (productL2Equiv.symm u).2 (productL2Equiv.symm v).2) := by
    intro u v
    simp only [chartChristoffelBilin_apply_normed]
    exact chartChristoffelContraction_productL2 I J g h p y u v hy
  have heq := covBilinDerivative_split (E := E) (F := F) (G := WithLp 2 (E × F)) productL2Equiv
    (ΓA := Riemannian.Jacobi.chartChristoffelBilin g p.1)
    (ΓB := Riemannian.Jacobi.chartChristoffelBilin h p.2)
    (ΓC := Riemannian.Jacobi.chartChristoffelBilin (productL2Metric I J g h) p)
    (A := chartRicciBilin g p.1) (B := chartRicciBilin h p.2)
    (C := chartRicciBilin (productL2Metric I J g h) p) (y := y)
    ((contDiffAt_chartRicciBilin g p.1 hxy.1).differentiableAt (by simp))
    ((contDiffAt_chartRicciBilin h p.2 hxy.2).differentiableAt (by simp))
    ((contDiffAt_chartRicciBilin (productL2Metric I J g h) p hy).differentiableAt (by simp))
    hsplit hΓ U V W
  rw [covBilinDerivative_chartRicci_eq_intrinsic _ _ hy,
    covBilinDerivative_chartRicci_eq_intrinsic _ _ hxy.1,
    covBilinDerivative_chartRicci_eq_intrinsic _ _ hxy.2] at heq
  have h0 : (extChartAt (productL2Model I J) p).symm y = p :=
    (extChartAt (productL2Model I J) p).left_inv (mem_extChartAt_source p)
  have hy1 : (productL2Equiv.symm y).1 = extChartAt I p.1 p.1 := by
    simp only [y, productL2_extChartAt, ContinuousLinearEquiv.symm_apply_apply,
      extChartAt_prod, PartialEquiv.prod_coe]
  have hy2 : (productL2Equiv.symm y).2 = extChartAt J p.2 p.2 := by
    simp only [y, productL2_extChartAt, ContinuousLinearEquiv.symm_apply_apply,
      extChartAt_prod, PartialEquiv.prod_coe]
  have h1 : (extChartAt I p.1).symm (productL2Equiv.symm y).1 = p.1 := by
    rw [hy1]; exact (extChartAt I p.1).left_inv (mem_extChartAt_source p.1)
  have h2 : (extChartAt J p.2).symm (productL2Equiv.symm y).2 = p.2 := by
    rw [hy2]; exact (extChartAt J p.2).left_inv (mem_extChartAt_source p.2)
  rw [h0, h1, h2] at heq
  simpa only [trivializationAt_symm_self] using heq

end Product
end CurveControl.Geometry.ProductCovRicci
