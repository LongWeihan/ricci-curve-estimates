import CurveControl.Geometry.AmbientTensorExpansion
import CurveControl.Geometry.ChartNormControl
import CurveControl.Geometry.AmbientBounds
import CurveControl.Geometry.AmbientTensorRegularity
import MorganTianLib.Ch03.RicciFlow.RiemannVariation

/-!
# Compactness construction for genuine ambient tensor bounds

Local coefficient bounds below are derived from smooth metric-family regularity
on a compact chart box and a closed time interval, including time endpoints.
The chart dual-vector estimate converts these to intrinsic metric-normalized
bounds. A finite precompact chart cover yields global constants without any
assumed tensor bound or model-norm/metric-norm identification.
-/
open scoped ContDiff Manifold Topology Bundle
open Set Filter Riemannian Riemannian.Tensor MorganTianLib
noncomputable section
set_option linter.unusedSectionVars false
namespace CurveControl.Geometry.CompactAmbientBounds

/-- **Math.** One bound controls a finite family of continuous scalar functions
on a compact set; no boundedness premise is required. -/
theorem exists_bound_finite_family {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {S : Set X} (hS : IsCompact S) (F : X → ι → ℝ)
    (hF : ∀ i, ContinuousOn (fun x => F x i) S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ i, |F x i| ≤ C := by
  have hcont : ContinuousOn F S := continuousOn_pi.mpr hF
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx i
  exact (norm_le_pi_norm (F x) i).trans ((hC x hx).trans (le_max_left _ _))

/-- **Math.** A weighted finite sum bound, used one tensor slot at a time. -/
theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (a f : ι → ℝ) (C : ℝ)
    (hf : ∀ i, |f i| ≤ C) :
    |∑ i, a i * f i| ≤ (∑ i, |a i|) * C := by
  calc
    _ ≤ ∑ i, |a i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * C := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- **Math.** A coefficient bound controls a double coordinate contraction. -/
theorem abs_sum_mul₂_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (T : ι → ι → ℝ) (C : ℝ) (hT : ∀ i j, |T i j| ≤ C) :
    |∑ i, ∑ j, a i * b j * T i j| ≤ (∑ i, |a i|) * ((∑ j, |b j|) * C) := by
  have h := abs_sum_mul_le a (fun i => ∑ j, b j * T i j)
    ((∑ j, |b j|) * C) (fun i => abs_sum_mul_le b (T i) C (hT i))
  simpa only [Finset.mul_sum, mul_assoc] using h

/-- **Math.** A coefficient bound controls a triple coordinate contraction. -/
theorem abs_sum_mul₃_le {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (T : ι → ι → ι → ℝ) (C : ℝ)
    (hT : ∀ i j k, |T i j k| ≤ C) :
    |∑ i, ∑ j, ∑ k, a i * b j * c k * T i j k| ≤
      (∑ i, |a i|) * ((∑ j, |b j|) * ((∑ k, |c k|) * C)) := by
  have h := abs_sum_mul_le a (fun i => ∑ j, ∑ k, b j * c k * T i j k)
    ((∑ j, |b j|) * ((∑ k, |c k|) * C))
    (fun i => abs_sum_mul₂_le b c (T i) C (hT i))
  simpa only [Finset.mul_sum, mul_assoc] using h

/-- **Math.** A coefficient bound controls a quadruple coordinate contraction. -/
theorem abs_sum_mul₄_le {ι : Type*} [Fintype ι]
    (a b c d : ι → ℝ) (T : ι → ι → ι → ι → ℝ) (C : ℝ)
    (hT : ∀ i j k l, |T i j k l| ≤ C) :
    |∑ i, ∑ j, ∑ k, ∑ l, a i * b j * c k * d l * T i j k l| ≤
      (∑ i, |a i|) * ((∑ j, |b j|) * ((∑ k, |c k|) * ((∑ l, |d l|) * C))) := by
  have h := abs_sum_mul_le a (fun i => ∑ j, ∑ k, ∑ l, b j * c k * d l * T i j k l)
    ((∑ j, |b j|) * ((∑ k, |c k|) * ((∑ l, |d l|) * C)))
    (fun i => abs_sum_mul₃_le b c d (T i) C (hT i))
  simpa only [Finset.mul_sum, mul_assoc] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Lowering the mixed curvature output index preserves joint
smoothness throughout the time set, including its endpoints. -/
theorem contDiffOn_chartRiemannCoefOnE_timeSpace
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => chartRiemannCoefOnE (g z.1) α i j k l z.2)
      (J ×ˢ (extChartAt I α).target) := by
  unfold chartRiemannCoefOnE
  exact ContDiffOn.sum fun m _ =>
    (contDiffOn_chartCurvatureCoef_timeSpace hg α i j k m).mul
      (contDiffOn_chartGramOnE_timeSpace hg α m l)

/-- **Math.** A finite bound for all inverse-metric entries on a compact chart
box and a closed time interval of a smooth metric family. -/
theorem exists_inverseGram_bound_on_compact_chart
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) {a b : ℝ} (hJ : Icc a b ⊆ J)
    {L : Set E} (hL : IsCompact L) (hchart : L ⊆ (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y ∈ L,
      ∀ i j : Fin (Module.finrank ℝ E), |chartInvGramOnE (g t) α i j y| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_finite_family (isCompact_Icc.prod hL)
    (fun (z : ℝ × E) (ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
      chartInvGramOnE (g z.1) α ij.1 ij.2 z.2)
    (fun ij => (contDiffOn_chartInvGramOnE_timeSpace hg α ij.1 ij.2).continuousOn.mono
      (Set.prod_mono hJ hchart))
  exact ⟨C, hC, fun t ht y hy i j => hbound (t, y) ⟨ht, hy⟩ (i, j)⟩

/-- **Math.** All actual Ricci coefficients have one finite compact-box bound. -/
theorem exists_ricci_bound_on_compact_chart
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) {a b : ℝ} (hJ : Icc a b ⊆ J)
    {L : Set E} (hL : IsCompact L) (hchart : L ⊆ (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y ∈ L,
      ∀ i j : Fin (Module.finrank ℝ E), |chartRicciCoefOnE (g t) α i j y| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_finite_family (isCompact_Icc.prod hL)
    (fun (z : ℝ × E) (ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
      chartRicciCoefOnE (g z.1) α ij.1 ij.2 z.2)
    (fun ij => (contDiffOn_chartRicciCoefOnE_timeSpace hg α ij.1 ij.2).continuousOn.mono
      (Set.prod_mono hJ hchart))
  exact ⟨C, hC, fun t ht y hy i j => hbound (t, y) ⟨ht, hy⟩ (i, j)⟩

/-- **Math.** All actual lowered Riemann coefficients have one finite compact-box bound. -/
theorem exists_riemann_bound_on_compact_chart
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) {a b : ℝ} (hJ : Icc a b ⊆ J)
    {L : Set E} (hL : IsCompact L) (hchart : L ⊆ (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y ∈ L,
      ∀ i j k l : Fin (Module.finrank ℝ E), |chartRiemannCoefOnE (g t) α i j k l y| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_finite_family (isCompact_Icc.prod hL)
    (fun (z : ℝ × E) (v : Fin 4 → Fin (Module.finrank ℝ E)) =>
      chartRiemannCoefOnE (g z.1) α (v 0) (v 1) (v 2) (v 3) z.2)
    (fun v => (contDiffOn_chartRiemannCoefOnE_timeSpace hg α (v 0) (v 1) (v 2) (v 3)).continuousOn.mono
      (Set.prod_mono hJ hchart))
  refine ⟨C, hC, ?_⟩
  intro t ht y hy i j k l
  simpa using hbound (t, y) ⟨ht, hy⟩ ![i, j, k, l]

/-- **Math.** All actual covariant-Ricci coefficients have one finite compact-box bound. -/
theorem exists_covRicci_bound_on_compact_chart
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) {a b : ℝ} (hJ : Icc a b ⊆ J)
    {L : Set E} (hL : IsCompact L) (hchart : L ⊆ (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y ∈ L,
      ∀ r i j : Fin (Module.finrank ℝ E), |chartCovRicciOnE (g t) α r i j y| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_finite_family (isCompact_Icc.prod hL)
    (fun (z : ℝ × E) (v : Fin 3 → Fin (Module.finrank ℝ E)) =>
      chartCovRicciOnE (g z.1) α (v 0) (v 1) (v 2) z.2)
    (fun v => (AmbientTensorRegularity.contDiffOn_chartCovRicciOnE_timeSpace
      hg α (v 0) (v 1) (v 2)).continuousOn.mono (Set.prod_mono hJ hchart))
  refine ⟨C, hC, ?_⟩
  intro t ht y hy r i j
  simpa using hbound (t, y) ⟨ht, hy⟩ ![r, i, j]

/-- **Math.** The sum of absolute chart coordinates is controlled by the actual metric. -/
theorem sum_abs_chartBasis_repr_le
    (g : Riemannian.RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {A : ℝ} (hA : ∀ i, chartInvGramMatrix g α p i i ≤ A)
    (v : TangentSpace I p) :
    (∑ i, |(chartBasisFamily α hp).repr v i|) ≤
      ((Module.finrank ℝ E : ℝ) * Real.sqrt A) * AmbientBounds.metricNorm g p v := by
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
        Real.sqrt A * AmbientBounds.metricNorm g p v :=
      Finset.sum_le_sum fun i _ => (abs_chartBasis_repr_le g α hp i v).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hA i))
          (AmbientBounds.metricNorm_nonneg _ _ _))
    _ = _ := by simp [mul_assoc]

/-- **Math.** Finite basis bounds imply intrinsic tensor bounds using the actual metric. -/
theorem tensorBoundsAt_of_chart_coefficients
    (g : Riemannian.RiemannianMetric I M) (α : M) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {A B K D : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (ha : ∀ i, chartInvGramMatrix g α p i i ≤ A)
    (hb : ∀ i j, |ricciTensorAt g p (chartBasisFamily α hp i) (chartBasisFamily α hp j)| ≤ B)
    (hk : ∀ i j k l, |AmbientBounds.rm g p (chartBasisFamily α hp i)
      (chartBasisFamily α hp j) (chartBasisFamily α hp k) (chartBasisFamily α hp l)| ≤ K)
    (hd : ∀ i j k, |AmbientBounds.covRic g p (chartBasisFamily α hp i)
      (chartBasisFamily α hp j) (chartBasisFamily α hp k)| ≤ D) :
    let F := (Module.finrank ℝ E : ℝ) * Real.sqrt A
    AmbientBounds.TensorBoundsAt g p (B * F ^ 2) (K * F ^ 4) (D * F ^ 3) := by
  classical
  let b := chartBasisFamily α hp
  let F := (Module.finrank ℝ E : ℝ) * Real.sqrt A
  have hF : 0 ≤ F := by positivity
  have hn (v : TangentSpace I p) : 0 ≤ AmbientBounds.metricNorm g p v :=
    AmbientBounds.metricNorm_nonneg _ _ _
  have hm (v : TangentSpace I p) : (∑ i, |b.repr v i|) ≤ F * AmbientBounds.metricNorm g p v :=
    sum_abs_chartBasis_repr_le g α hp ha v
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · intro u v
    have he : ricciTensorAt g p u v = ∑ i, ∑ j,
        b.repr u i * b.repr v j * ricciTensorAt g p (b i) (b j) := by
      conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    calc
      _ ≤ (∑ i, |b.repr u i|) * ((∑ j, |b.repr v j|) * B) :=
        abs_sum_mul₂_le _ _ _ _ hb
      _ ≤ (F * AmbientBounds.metricNorm g p u) * ((F * AmbientBounds.metricNorm g p v) * B) := by
        gcongr <;> first | exact hm _ | exact mul_nonneg hF (hn _)
      _ = _ := by dsimp [F]; ring
  · intro u v w z
    change |curvatureFormAt g g.leviCivitaConnection p u v w z| ≤ _
    rw [AmbientTensorExpansion.curvatureFormAt_basis_expand g g.leviCivitaConnection p b]
    calc
      _ ≤ (∑ i, |b.repr u i|) * ((∑ j, |b.repr v j|) *
          ((∑ k, |b.repr w k|) * ((∑ l, |b.repr z l|) * K))) :=
        abs_sum_mul₄_le _ _ _ _ _ _ hk
      _ ≤ (F * AmbientBounds.metricNorm g p u) * ((F * AmbientBounds.metricNorm g p v) *
          ((F * AmbientBounds.metricNorm g p w) * ((F * AmbientBounds.metricNorm g p z) * K))) := by
        gcongr <;> first | exact hm _ | exact mul_nonneg hF (hn _)
      _ = _ := by dsimp [F]; ring
  · intro u v w
    unfold AmbientBounds.covRic
    rw [AmbientTensorExpansion.covRicciAt_basis_expand _ _ _ p b]
    calc
      _ ≤ (∑ i, |b.repr u i|) * ((∑ j, |b.repr v j|) * ((∑ k, |b.repr w k|) * D)) :=
        abs_sum_mul₃_le _ _ _ _ _ hd
      _ ≤ (F * AmbientBounds.metricNorm g p u) * ((F * AmbientBounds.metricNorm g p v) *
          ((F * AmbientBounds.metricNorm g p w) * D)) := by
        gcongr <;> first | exact hm _ | exact mul_nonneg hF (hn _)
      _ = _ := by dsimp [F]; ring

/-- **Math.** Compact coordinate coefficient bounds give uniform intrinsic bounds
on the part of a chart mapped into the compact box. -/
theorem exists_tensorBounds_on_compact_chart
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M) {a b : ℝ} (hJ : Icc a b ⊆ J)
    {L : Set E} (hL : IsCompact L) (hchart : L ⊆ (extChartAt I α).target) :
    ∃ B K D : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ D ∧
      ∀ t ∈ Icc a b, ∀ p ∈ (extChartAt I α).source, extChartAt I α p ∈ L →
        AmbientBounds.TensorBoundsAt (g t) p B K D := by
  obtain ⟨A, hA, ha⟩ := exists_inverseGram_bound_on_compact_chart hg α hJ hL hchart
  obtain ⟨B, hB, hb⟩ := exists_ricci_bound_on_compact_chart hg α hJ hL hchart
  obtain ⟨K, hK, hk⟩ := exists_riemann_bound_on_compact_chart hg α hJ hL hchart
  obtain ⟨D, hD, hd⟩ := exists_covRicci_bound_on_compact_chart hg α hJ hL hchart
  let F := (Module.finrank ℝ E : ℝ) * Real.sqrt A
  refine ⟨B * F ^ 2, K * F ^ 4, D * F ^ 3, by positivity, by positivity, by positivity, ?_⟩
  intro t ht p hp hLp
  have hp' : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source
    rwa [← extChartAt_source (𝕜 := ℝ) (E := E) I α]
  have hy := (extChartAt I α).map_source hp
  have he := (extChartAt I α).left_inv hp
  apply tensorBoundsAt_of_chart_coefficients (g t) α hp' hA hB hK hD
  · intro i
    have hi := (le_abs_self _).trans (ha t ht _ hLp i i)
    simpa only [chartInvGramOnE_def, he] using hi
  · intro i j
    have hi := hb t ht _ hLp i j
    rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis (g t) α i j hy, he] at hi
    simpa only [chartBasisFamily_apply] using hi
  · intro i j k l
    have hi := hk t ht _ hLp i j k l
    rw [chartRiemannCoefOnE_eq_curvatureFormAt_chartBasis (g t) α i j k l hy, he] at hi
    simpa only [chartBasisFamily_apply, AmbientBounds.rm] using hi
  · intro i j k
    have hi := hd t ht _ hLp i j k
    rw [chartCovRicciOnE_eq_covRicciAt_chartBasis (g t) α i j k hy, he] at hi
    simpa only [chartBasisFamily_apply, AmbientBounds.covRic] using hi

/-- **Math.** A compact manifold admits finitely many open chart neighborhoods,
each mapped into a compact model-space box contained in the same chart target. -/
theorem exists_finite_compact_chart_cover [CompactSpace M] :
    ∃ (s : Finset M) (L : M → Set E) (U : M → Set M),
      (∀ p, IsCompact (L p)) ∧
      (∀ p, L p ⊆ (extChartAt I p).target) ∧
      (∀ p, IsOpen (U p)) ∧
      (∀ p, U p ⊆ (extChartAt I p).source) ∧
      (∀ p, MapsTo (extChartAt I p) (U p) (L p)) ∧
      (Set.univ : Set M) ⊆ ⋃ p ∈ s, U p := by
  classical
  have hlocal (p : M) : ∃ (L : Set E) (U : Set M), IsCompact L ∧
      L ⊆ (extChartAt I p).target ∧ IsOpen U ∧ p ∈ U ∧
      U ⊆ (extChartAt I p).source ∧ MapsTo (extChartAt I p) U L := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_extChartAt_target (I := I) p) (extChartAt I p p) (mem_extChartAt_target p)
    let L := Metric.closedBall (extChartAt I p p) (r / 2)
    let U := (extChartAt I p).source ∩
      (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) (r / 2)
    refine ⟨L, U, isCompact_closedBall _ _, ?_, ?_, ?_, inter_subset_left, ?_⟩
    · exact (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
    · exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
        (isOpen_extChartAt_source p) Metric.isOpen_ball
    · exact ⟨mem_extChartAt_source p, Metric.mem_ball_self (by linarith)⟩
    · intro q hq
      exact Metric.ball_subset_closedBall hq.2
  choose L U hLc hLt hUo hpU hUs hUL using hlocal
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
    U hUo (fun p _ => Set.mem_iUnion.mpr ⟨p, hpU p⟩)
  exact ⟨s, L, U, hLc, hLt, hUo, hUs, hUL, hs⟩

/-- **Math.** Increasing nonnegative intrinsic constants preserves each tensor estimate. -/
theorem tensorBoundsAt_mono
    {g : Riemannian.RiemannianMetric I M} {p : M} {B K D B' K' D' : ℝ}
    (h : AmbientBounds.TensorBoundsAt g p B K D)
    (hB : B ≤ B') (hK : K ≤ K') (hD : D ≤ D') :
    AmbientBounds.TensorBoundsAt g p B' K' D' := by
  refine ⟨h.ricci_nonneg.trans hB, h.curvature_nonneg.trans hK,
    h.covRic_nonneg.trans hD, ?_, ?_, ?_⟩
  · intro u v
    exact (h.ricci u v).trans (by
      gcongr <;> exact AmbientBounds.metricNorm_nonneg _ _ _)
  · intro u v w z
    exact (h.curvature u v w z).trans (by
      gcongr <;> exact AmbientBounds.metricNorm_nonneg _ _ _)
  · intro u v w
    exact (h.covRic u v w).trans (by
      gcongr <;> exact AmbientBounds.metricNorm_nonneg _ _ _)

/-- **Math.** Finite spatial localization gives constants uniform over all space and time. -/
theorem uniformTensorBoundsOn_of_finite_cover
    {g : ℝ → Riemannian.RiemannianMetric I M} {T : Set ℝ}
    (s : Finset M) (U : M → Set M) (hcover : (Set.univ : Set M) ⊆ ⋃ α ∈ s, U α)
    (B K D : M → ℝ) (hB : ∀ α, 0 ≤ B α) (hK : ∀ α, 0 ≤ K α)
    (hD : ∀ α, 0 ≤ D α)
    (hlocal : ∀ α ∈ s, ∀ t ∈ T, ∀ p ∈ U α,
      AmbientBounds.TensorBoundsAt (g t) p (B α) (K α) (D α)) :
    AmbientBounds.UniformTensorBoundsOn g T (∑ α ∈ s, B α)
      (∑ α ∈ s, K α) (∑ α ∈ s, D α) := by
  classical
  intro t ht p
  obtain ⟨α, hα, hp⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ p))
  exact tensorBoundsAt_mono (hlocal α hα t ht p hp)
    (Finset.single_le_sum (fun α _ => hB α) hα)
    (Finset.single_le_sum (fun α _ => hK α) hα)
    (Finset.single_le_sum (fun α _ => hD α) hα)

/-- **Math.** Smoothness of the actual metric family on a compact manifold
constructs finite uniform bounds for Ricci, Riemann, and covariant Ricci on any
closed time interval contained in its time set. No tensor boundedness is assumed. -/
theorem exists_uniformTensorBoundsOn [CompactSpace M]
    {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) {a b : ℝ} (hJ : Icc a b ⊆ J) :
    ∃ B K D : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ D ∧
      AmbientBounds.UniformTensorBoundsOn g (Icc a b) B K D := by
  classical
  obtain ⟨s, L, U, hLc, hLt, _hUo, hUs, hUL, hcover⟩ :=
    exists_finite_compact_chart_cover (I := I) (M := M)
  have hlocal (α : M) := exists_tensorBounds_on_compact_chart hg α hJ (hLc α) (hLt α)
  choose B K D hB hK hD hbounds using hlocal
  refine ⟨∑ α ∈ s, B α, ∑ α ∈ s, K α, ∑ α ∈ s, D α,
    Finset.sum_nonneg (fun α _ => hB α), Finset.sum_nonneg (fun α _ => hK α),
    Finset.sum_nonneg (fun α _ => hD α), ?_⟩
  apply uniformTensorBoundsOn_of_finite_cover s U hcover B K D hB hK hD
  intro α _hα t ht p hp
  exact hbounds α t ht p (hUs α hp) (hUL α hp)

end CurveControl.Geometry.CompactAmbientBounds

