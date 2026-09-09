import CurveControl.Analysis.IntegralEstimates
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Smooth input supplies integral domination

All bounds below are extracted from compact rectangles. Geometric callers
provide joint regularity, never a separate domination hypothesis.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

namespace CurveControl.Analysis

theorem continuousOn_space_slice {f : ℝ → ℝ → ℝ} {a b u : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hu : u ∈ Icc a b) : ContinuousOn (f u) (Icc (0 : ℝ) 1) :=
  hf.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨hu, hx⟩)

theorem continuousOn_weightedIntegral_of_rectangle {f v : ℝ → ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hv : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun u => ∫ x in (0 : ℝ)..1, f u x * v u x) (Icc a b) := by
  have hp := hf.mul hv
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hp.norm
  apply continuousOn_weightedIntegral (bound := fun _ => M)
  · intro u hu
    exact ((continuousOn_space_slice hf hu).mul (continuousOn_space_slice hv hu)).mono
      Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  · intro u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hM ⟨(u, x), ⟨hu, Ioc_subset_Icc_self hx⟩, rfl⟩
  · exact intervalIntegrable_const.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hp.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ hu => ⟨hu, Ioc_subset_Icc_self hx⟩)

/-- An intermediate rectangle criterion: continuous derivative fields and
actual slice derivatives supply every domination/measurability requirement. -/
noncomputable def movingWeightData_of_rectangle
    {f v ft vt : ℝ → ℝ → ℝ} {a b t : ℝ}
    (ht : Icc a b ∈ 𝓝 t)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hv : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hft : ContinuousOn (Function.uncurry ft) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hvt : ContinuousOn (Function.uncurry vt) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hfd : ∀ u ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun z => f z x) (ft u x) u)
    (hvd : ∀ u ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun z => v z x) (vt u x) u) :
    MovingWeightData f v ft vt t := by
  apply Classical.choice
  have hdc := (hft.mul hv).add (hf.mul hvt)
  have hti : t ∈ Icc a b := mem_of_mem_nhds ht
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hdc.norm
  refine ⟨?_⟩
  refine ⟨Icc a b, (fun _ => M), ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ht] with u hu
    exact ((continuousOn_space_slice hf hu).mul (continuousOn_space_slice hv hu)).mono
      Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  · exact (ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      ((continuousOn_space_slice hf hti).mul (continuousOn_space_slice hv hti))).1
  · exact (((continuousOn_space_slice hft hti).mul (continuousOn_space_slice hv hti)).add
      ((continuousOn_space_slice hf hti).mul (continuousOn_space_slice hvt hti))).mono
      Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro u hu
    exact hM ⟨(u, x), ⟨hu, Ioc_subset_Icc_self hx⟩, rfl⟩
  · exact intervalIntegrable_const.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact fun u hu => hfd u hu x (Ioc_subset_Icc_self hx)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact fun u hu => hvd u hu x (Ioc_subset_Icc_self hx)

theorem hasDerivAt_time_slice_of_contDiffOn {f : ℝ → ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (U ×ˢ univ))
    {u x : ℝ} (hu : u ∈ U) :
    HasDerivAt (fun z => f z x) (fderiv ℝ (Function.uncurry f) (u, x) (1, 0)) u := by
  have hd := (hf.differentiableOn (by simp) (u, x) ⟨hu, mem_univ x⟩).differentiableAt ((hU.prod isOpen_univ).mem_nhds ⟨hu, mem_univ x⟩)
  have he : HasDerivAt (fun z : ℝ => (z, x)) ((1, 0) : ℝ × ℝ) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u x)
  exact hd.hasFDerivAt.comp_hasDerivAt u he

theorem continuousOn_time_deriv_of_contDiffOn {f : ℝ → ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (U ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun z => f z p.2) p.1) (U ×ˢ univ) := by
  have hc := (hf.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).clm_apply (continuousOn_const (c := ((1, 0) : ℝ × ℝ)))
  apply hc.congr
  intro p hp
  exact (hasDerivAt_time_slice_of_contDiffOn hU hf (x := p.2) hp.1).deriv

/-- Joint C1 regularity on an open time strip automatically supplies the
moving-weight data, using a compact time neighborhood and compact space. -/
noncomputable def movingWeightData_of_contDiffOn {f v : ℝ → ℝ → ℝ} {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (ht : t ∈ U)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (U ×ˢ univ))
    (hv : ContDiffOn ℝ 1 (Function.uncurry v) (U ×ˢ univ)) :
    MovingWeightData f v (fun u x => deriv (fun z => f z x) u)
      (fun u x => deriv (fun z => v z x) u) t := by
  apply Classical.choice
  obtain ⟨a, b, _, hn, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds ht)
  have hs : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ U ×ˢ univ :=
    fun _ hp => ⟨hsub hp.1, mem_univ _⟩
  refine ⟨?_⟩
  apply movingWeightData_of_rectangle
    (ft := fun u x => deriv (fun z => f z x) u)
    (vt := fun u x => deriv (fun z => v z x) u)
    hn (hf.continuousOn.mono hs) (hv.continuousOn.mono hs)
    ((continuousOn_time_deriv_of_contDiffOn hU hf).mono hs)
    ((continuousOn_time_deriv_of_contDiffOn hU hv).mono hs)
  · intro u hu x _
    exact (hasDerivAt_time_slice_of_contDiffOn hU hf (hsub hu)).differentiableAt.hasDerivAt
  · intro u hu x _
    exact (hasDerivAt_time_slice_of_contDiffOn hU hv (hsub hu)).differentiableAt.hasDerivAt

/-- Direct first variation from joint C1 regularity. All domination and
measurability assumptions have been discharged internally. -/
theorem hasDerivAt_weightedIntegral_of_contDiffOn {f v : ℝ → ℝ → ℝ} {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (ht : t ∈ U)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (U ×ˢ univ))
    (hv : ContDiffOn ℝ 1 (Function.uncurry v) (U ×ˢ univ)) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, f u x * v u x)
      (∫ x in (0 : ℝ)..1,
        deriv (fun z => f z x) t * v t x + f t x * deriv (fun z => v z x) t) t :=
  (movingWeightData_of_contDiffOn hU ht hf hv).hasDerivAt

end CurveControl.Analysis

#print axioms CurveControl.Analysis.continuousOn_space_slice
#print axioms CurveControl.Analysis.continuousOn_weightedIntegral_of_rectangle
#print axioms CurveControl.Analysis.movingWeightData_of_rectangle
#print axioms CurveControl.Analysis.hasDerivAt_time_slice_of_contDiffOn
#print axioms CurveControl.Analysis.continuousOn_time_deriv_of_contDiffOn
#print axioms CurveControl.Analysis.movingWeightData_of_contDiffOn
#print axioms CurveControl.Analysis.hasDerivAt_weightedIntegral_of_contDiffOn
