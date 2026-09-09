import MorganTianLib.Ch03.RicciFlow.ScalarSpacetimeSmooth
import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution

/-!
Joint regularity of the actual ambient Ricci tensor and its covariant derivative.
The time set need not be open. The spatial differentiation lemma is adapted
from the private lemma in MorganTianLib.Ch03.RicciFlow.ScalarSpacetimeSmooth;
spatial chart targets are open, so time endpoints require no extension.
-/
open scoped ContDiff Manifold Topology Bundle
open Set Filter Riemannian Riemannian.Tensor Riemannian.Geodesic MorganTianLib
noncomputable section
namespace CurveControl.Geometry.AmbientTensorRegularity

/-- Spatial differentiation preserves joint smoothness on an arbitrary time set. -/
theorem contDiffOn_spatialFDeriv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : Set ℝ} {U : Set E} (hU : IsOpen U) {F : ℝ × E → ℝ}
    (hF : ContDiffOn ℝ ∞ F (J ×ˢ U)) (v : E) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1, y)) z.2 v)
      (J ×ˢ U) := by
  let S : Set (ℝ × E) := J ×ˢ U
  let P : (ℝ × E) → E → ℝ := fun z y => F (z.1, y)
  let gs : (ℝ × E) → E := fun z => z.2
  let ks : (ℝ × E) → E := fun _ => v
  have hP : ContDiffOn ℝ ∞ (Function.uncurry P) (S ×ˢ U) := by
    change ContDiffOn ℝ ∞
      (fun w : (ℝ × E) × E => F (w.1.1, w.2)) (S ×ˢ U)
    have hmap : ContDiffOn ℝ ∞
        (fun w : (ℝ × E) × E => (w.1.1, w.2)) (S ×ˢ U) :=
      contDiffOn_fst.fst.prodMk contDiffOn_snd
    exact hF.comp hmap (fun _ hw => ⟨hw.1.1, hw.2⟩)
  intro z hz
  have hgs : ContDiffWithinAt ℝ ∞ gs S z := contDiffWithinAt_snd
  have hks : ContDiffWithinAt ℝ ∞ ks S z := contDiffWithinAt_const
  have hpartial := (hP (z, gs z) ⟨hz, hz.2⟩).fderivWithin_apply
    hgs hks hU.uniqueDiffOn
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ from le_rfl) hz (by
      intro w hw
      exact hw.2)
  refine hpartial.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [fderivWithin_of_isOpen hU hw.2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Covariant Ricci coefficients are jointly smooth on the whole time set. -/
theorem contDiffOn_chartCovRicciOnE_timeSpace
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (r i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartCovRicciOnE (I := I) (g z.1) α r i j z.2)
      (J ×ˢ (extChartAt I α).target) := by
  classical
  have hRic := contDiffOn_chartRicciCoefOnE_timeSpace hg α
  have hΓ := contDiffOn_chartChristoffel_timeSpace_on_timeSet hg α
  have hpartial : ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (chartRicciCoefOnE (I := I) (g z.1) α i j) z.2)
      (J ×ˢ (extChartAt I α).target) := by
    simpa only [partialDeriv] using contDiffOn_spatialFDeriv_apply
      (isOpen_extChartAt_target (I := I) α) (hRic i j) ((Module.finBasis ℝ E) r)
  unfold chartCovRicciOnE
  exact (hpartial.sub (ContDiffOn.sum fun s _ => (hΓ r i s).mul (hRic s j))).sub
    (ContDiffOn.sum fun s _ => (hΓ r j s).mul (hRic i s))

/-- Coordinate coefficients of ∇Ric are continuous including time endpoints. -/
theorem continuousOn_chartCovRicciOnE_timeSpace
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (r i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun z : ℝ × E => chartCovRicciOnE (I := I) (g z.1) α r i j z.2)
      (J ×ˢ (extChartAt I α).target) :=
  (contDiffOn_chartCovRicciOnE_timeSpace hg α r i j).continuousOn

section Intrinsic
variable [SigmaCompactSpace M] [T2Space M]

/-- Canonical intrinsic covariant derivative of Ricci, with its actual
Levi-Civita connection and proved Levi-Civita property. -/
def actualCovRicci (g : Riemannian.RiemannianMetric I M) (p : M)
    (u v w : TangentSpace I p) : ℝ :=
  covRicciAt g g.leviCivitaConnection
    (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)) p u v w

/-- Actual ∇Ric evaluated on the fixed chart frame. -/
def actualCovRicciChartCoef (g : Riemannian.RiemannianMetric I M) (α : M)
    (r i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  actualCovRicci g ((extChartAt I α).symm y)
    (chartBasisVecFiber (I := I) α r ((extChartAt I α).symm y))
    (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
    (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))

theorem actualCovRicciChartCoef_eq (g : Riemannian.RiemannianMetric I M) (α : M)
    (r i j : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ (extChartAt I α).target) :
    actualCovRicciChartCoef g α r i j y = chartCovRicciOnE (I := I) g α r i j y :=
  (chartCovRicciOnE_eq_covRicciAt_chartBasis g α r i j hy).symm

/-- Joint smoothness is a property of the actual intrinsic ∇Ric coefficients. -/
theorem contDiffOn_actualCovRicciChartCoef
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (r i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => actualCovRicciChartCoef (g z.1) α r i j z.2)
      (J ×ˢ (extChartAt I α).target) := by
  apply (contDiffOn_chartCovRicciOnE_timeSpace hg α r i j).congr
  intro z hz
  exact actualCovRicciChartCoef_eq (g z.1) α r i j hz.2

/-- Actual Ricci evaluated on a fixed chart frame. -/
def actualRicciChartCoef (g : Riemannian.RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ricciTensorAt g ((extChartAt I α).symm y)
    (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
    (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))

theorem contDiffOn_actualRicciChartCoef
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => actualRicciChartCoef (g z.1) α i j z.2)
      (J ×ˢ (extChartAt I α).target) := by
  apply (contDiffOn_chartRicciCoefOnE_timeSpace hg α i j).congr
  intro z hz
  exact (chartRicciCoefOnE_eq_ricciTensorAt_chartBasis (g z.1) α i j hz.2).symm

/-- Continuous intrinsic ∇Ric chart coefficients for compactness arguments. -/
theorem continuousOn_actualCovRicciChartCoef
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) (r i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun z : ℝ × E => actualCovRicciChartCoef (g z.1) α r i j z.2)
      (J ×ˢ (extChartAt I α).target) :=
  (contDiffOn_actualCovRicciChartCoef hg α r i j).continuousOn

end Intrinsic
end CurveControl.Geometry.AmbientTensorRegularity
