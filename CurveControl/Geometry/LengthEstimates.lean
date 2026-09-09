import CurveControl.Geometry.SpeedEvolution
import CurveControl.Geometry.CurveRegularity
import CurveControl.Analysis.SmoothIntegral
import CurveControl.Analysis.InteriorComparison

open Set Filter MeasureTheory Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff Interval
noncomputable section
namespace CurveControl.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The actual geometric length first-variation integral. -/
def lengthRate (g : ℝ → Riemannian.RiemannianMetric I M) (c : ℝ → ℝ → M)
    (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    -(curvatureSq (g t) (c t) x + ricciTensorAt (g t) (c t x)
      (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x)) *
      curveSpeed (g t) (c t) x

namespace IsCurveShorteningFlowOn
variable {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
  (hc : IsCurveShorteningFlowOn (I := I) g c J) (hflow : IsRicciFlowOn g J)
include hc hflow

/-- **Math.** Joint smoothness supplies the analytic C1 open-strip input. -/
theorem contDiffOn_curveSpeed_interior :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => curveSpeed (g p.1) (c p.1) p.2)
      (interior J ×ˢ univ) := by
  intro p hp
  exact (contDiffAt_infty.mp (hc.contDiffAt_curveSpeed hflow.smooth hp.1) 1).contDiffWithinAt

/-- **Math.** Length is continuous on every closed time interval in the flow domain. -/
theorem continuousOn_curveLength {a b : ℝ} (hab : Icc a b ⊆ J) :
    ContinuousOn (fun t => curveLength (g t) (c t)) (Icc a b) := by
  have h := Analysis.continuousOn_weightedIntegral_of_rectangle
    (f := fun _ _ => (1 : ℝ)) (v := fun t x => curveSpeed (g t) (c t) x) continuousOn_const
    (hc.continuousOn_curveSpeed_rectangle hflow.smooth (uniqueDiffOn_ricciTime hflow) hab)
  simpa only [one_mul, curveLength] using h

/-- **Math.** The curvature-energy function is continuous up to included endpoints. -/
theorem continuousOn_curvatureEnergy {a b : ℝ} (hab : Icc a b ⊆ J) :
    ContinuousOn (fun t => curvatureEnergy (g t) (c t)) (Icc a b) :=
  Analysis.continuousOn_weightedIntegral_of_rectangle
    (hc.continuousOn_curvatureSq_rectangle hflow.smooth (uniqueDiffOn_ricciTime hflow) hab)
    (hc.continuousOn_curveSpeed_rectangle hflow.smooth (uniqueDiffOn_ricciTime hflow) hab)

/-- **Math.** Differentiation under the length integral follows from joint C1
regularity; the geometric integrand follows from the proved speed evolution. -/
theorem hasDerivAt_curveLength {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => curveLength (g s) (c s)) (lengthRate g c t) t := by
  have h := Analysis.hasDerivAt_weightedIntegral_of_contDiffOn
    (f := fun _ _ => (1 : ℝ)) (v := fun t x => curveSpeed (g t) (c t) x) isOpen_interior ht contDiffOn_const
    (hc.contDiffOn_curveSpeed_interior hflow)
  simp only [deriv_const, zero_mul, one_mul, zero_add] at h
  apply h.congr_deriv
  apply intervalIntegral.integral_congr
  intro x _
  exact (hc.hasDerivAt_curveSpeed_time hflow ht x).deriv

/-- **Math.** The actual first-variation density is integrable on one spatial period. -/
theorem intervalIntegrable_lengthDensity {t : ℝ} (ht : t ∈ interior J) :
    IntervalIntegrable (fun x =>
      -(curvatureSq (g t) (c t) x + ricciTensorAt (g t) (c t x)
        (unitTangent (g t) (c t) x) (unitTangent (g t) (c t) x)) *
        curveSpeed (g t) (c t) x) volume 0 1 := by
  have hd := Analysis.continuousOn_time_deriv_of_contDiffOn
    (f := fun t x => curveSpeed (g t) (c t) x) isOpen_interior
    (hc.contDiffOn_curveSpeed_interior hflow)
  have hs : ContinuousOn (fun x => deriv (fun z => curveSpeed (g z) (c z) x) t)
      (Icc (0 : ℝ) 1) :=
    hd.comp (continuousOn_const.prodMk continuousOn_id) (by intro x _; exact ⟨ht, mem_univ x⟩)
  have hi := hs.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  apply hi.congr
  intro x _
  exact (hc.hasDerivAt_curveSpeed_time hflow ht x).deriv

omit [SigmaCompactSpace M] [T2Space M] hc hflow in
/-- **Math.** Curvature energy is nonnegative for the actual metric quantities. -/
theorem curvatureEnergy_nonneg (t : ℝ) : 0 ≤ curvatureEnergy (g t) (c t) := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x _
  exact mul_nonneg (curvatureSq_nonneg _ _ _) (curveSpeed_nonneg _ _ _)

/-- **Math.** An ambient Ricci lower bound on all unit vectors gives the length
loss inequality with the full actual curvature energy retained. -/
theorem lengthRate_le_growth_sub_energy {t B : ℝ} (ht : t ∈ interior J)
    (hRic : ∀ (p : M) (V : TangentSpace I p),
      (g t).metricInner p V V = 1 → -B ≤ ricciTensorAt (g t) p V V) :
    lengthRate g c t ≤ B * curveLength (g t) (c t) - curvatureEnergy (g t) (c t) := by
  have hv : ContinuousOn (curveSpeed (g t) (c t)) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact ((hc.contDiffAt_curveSpeed hflow.smooth (p := (t, x)) ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hq : ContinuousOn (curvatureSq (g t) (c t)) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact ((hc.contDiffAt_curvatureSq hflow.smooth (p := (t, x)) ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hvi := hv.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hqvi := (hq.mul hv).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hmono := intervalIntegral.integral_mono_on zero_le_one
    (hc.intervalIntegrable_lengthDensity hflow ht) ((hvi.const_mul B).sub hqvi)
    (fun x hx => by
      have hr := hRic (c t x) (unitTangent (g t) (c t) x)
        (hc.tangent_unit (interior_subset ht) x)
      have hpos := curveSpeed_nonneg (g t) (c t) x
      simp only [Pi.mul_apply]
      nlinarith)
  rw [intervalIntegral.integral_sub (hvi.const_mul B) hqvi,
    intervalIntegral.integral_const_mul] at hmono
  simpa only [Pi.mul_apply, lengthRate, curveLength, curvatureEnergy] using hmono

/-- **Math.** Exponential length bound from the actual flow and an ambient
Ricci lower bound. No geometric differential inequality is an input. -/
theorem curveLength_le_exp {a b B : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ J)
    (hRic : ∀ t ∈ Icc a b, ∀ (p : M) (V : TangentSpace I p),
      (g t).metricInner p V V = 1 → -B ≤ ricciTensorAt (g t) p V V) :
    curveLength (g b) (c b) ≤ curveLength (g a) (c a) * Real.exp (B * (b - a)) := by
  have hJi : Ioo a b ⊆ interior J := by
    intro t ht
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hJ)
  apply Analysis.le_exp_of_deriv_interior_le hab (hc.continuousOn_curveLength hflow hJ)
    (fun t ht => (hc.hasDerivAt_curveLength hflow (hJi ht)).hasDerivWithinAt)
  intro t ht
  have hd := hc.lengthRate_le_growth_sub_energy hflow (hJi ht) (hRic t (Ioo_subset_Icc_self ht))
  have he := curvatureEnergy_nonneg (g := g) (c := c) t
  linarith

/-- **Math.** The length bound holds uniformly throughout the closed time interval. -/
theorem curveLength_le_exp_on {a b B : ℝ} (hJ : Icc a b ⊆ J)
    (hRic : ∀ t ∈ Icc a b, ∀ (p : M) (V : TangentSpace I p),
      (g t).metricInner p V V = 1 → -B ≤ ricciTensorAt (g t) p V V) :
    ∀ t ∈ Icc a b, curveLength (g t) (c t) ≤
      curveLength (g a) (c a) * Real.exp (B * (t - a)) := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  exact hc.curveLength_le_exp hflow ht.1 (hsub.trans hJ)
    (fun u hu => hRic u (hsub hu))

/-- **Math.** The weighted time integral of the actual curvature energy is
bounded by the integrating-factor loss of actual curve length. -/
theorem weighted_curvatureEnergy_integral_le {a b B : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ J)
    (hRic : ∀ t ∈ Icc a b, ∀ (p : M) (V : TangentSpace I p),
      (g t).metricInner p V V = 1 → -B ≤ ricciTensorAt (g t) p V V) :
    (∫ t in a..b, Real.exp (-B * (t - a)) * curvatureEnergy (g t) (c t)) ≤
      curveLength (g a) (c a) - Real.exp (-B * (b - a)) * curveLength (g b) (c b) := by
  have hJi : Ioo a b ⊆ interior J := by
    intro t ht
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hJ)
  exact Analysis.weighted_energy_integral_le hab
    (hc.continuousOn_curveLength hflow hJ)
    (fun t ht => (hc.hasDerivAt_curveLength hflow (hJi ht)).hasDerivWithinAt)
    ((hc.continuousOn_curvatureEnergy hflow hJ).integrableOn_Icc)
    (fun t ht => hc.lengthRate_le_growth_sub_energy hflow (hJi ht)
      (hRic t (Ioo_subset_Icc_self ht)))

/-- **Math.** Unweighted accumulated curvature energy under a nonnegative
ambient Ricci-bound constant. All integrability follows from smooth flow. -/
theorem curvatureEnergy_integral_le {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hJ : Icc a b ⊆ J)
    (hRic : ∀ t ∈ Icc a b, ∀ (p : M) (V : TangentSpace I p),
      (g t).metricInner p V V = 1 → -B ≤ ricciTensorAt (g t) p V V) :
    (∫ t in a..b, curvatureEnergy (g t) (c t)) ≤
      Real.exp (B * (b - a)) * curveLength (g a) (c a) - curveLength (g b) (c b) := by
  have hJi : Ioo a b ⊆ interior J := by
    intro t ht
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hJ)
  exact Analysis.energy_integral_le hab
    (hc.continuousOn_curveLength hflow hJ)
    (fun t ht => (hc.hasDerivAt_curveLength hflow (hJi ht)).hasDerivWithinAt)
    ((hc.continuousOn_curvatureEnergy hflow hJ).integrableOn_Icc)
    (fun t ht => hc.lengthRate_le_growth_sub_energy hflow (hJi ht)
      (hRic t (Ioo_subset_Icc_self ht))) hB (fun t _ => curvatureEnergy_nonneg (g := g) (c := c) t)

end IsCurveShorteningFlowOn
#print axioms IsCurveShorteningFlowOn.hasDerivAt_curveLength
#print axioms IsCurveShorteningFlowOn.curveLength_le_exp
#print axioms IsCurveShorteningFlowOn.curveLength_le_exp_on
#print axioms IsCurveShorteningFlowOn.weighted_curvatureEnergy_integral_le
#print axioms IsCurveShorteningFlowOn.curvatureEnergy_integral_le
end CurveControl.Geometry
