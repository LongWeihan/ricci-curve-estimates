import CurveControl.Analysis.SmoothIntegral
import CurveControl.Analysis.RegularizedPDE
import CurveControl.Analysis.InteriorComparison
import CurveControl.Analysis.RegularizedIntegral

/-! # Complete scalar curve-estimate assembly

This is an analysis theorem with explicit squared-curvature PDE and Kato
inputs. Those two inputs and the density evolution must be proved by the
geometry layer. Regularized PDEs, domination, integral differential
inequalities, and regularization limits are all proved internally.
Time derivatives are required only in the open time interval.
-/

open MeasureTheory Filter Set
open scoped Topology Interval ContDiff

namespace CurveControl.Analysis

structure ScalarCurveHypotheses (q v r P : ℝ → ℝ → ℝ) (a b A B : ℝ) : Prop where
  q_smooth : ContDiffOn ℝ ∞ (Function.uncurry q) (Ioo a b ×ˢ univ)
  v_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Ioo a b ×ˢ univ)
  q_continuous : ContinuousOn (Function.uncurry q) (Icc a b ×ˢ Icc (0 : ℝ) 1)
  v_continuous : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ Icc (0 : ℝ) 1)
  q_nonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ q t x
  v_pos : ∀ t ∈ Icc a b, ∀ x, 0 < v t x
  q_periodic : ∀ t ∈ Ioo a b, Function.Periodic (q t) 1
  v_periodic : ∀ t ∈ Ioo a b, Function.Periodic (v t) 1
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  ricci_bound : ∀ t ∈ Ioo a b, ∀ x, |r t x| ≤ B
  density_evolution : ∀ t ∈ Ioo a b, ∀ x,
    deriv (fun u => v u x) t = -(q t x + r t x) * v t x
  kato : ∀ t ∈ Ioo a b, ∀ x,
    (arcDeriv (v t) (q t) x) ^ 2 ≤ 4 * q t x * (P t x) ^ 2
  squared_pde : ∀ t ∈ Ioo a b, ∀ x,
    deriv (fun u => q u x) t ≤ arcDeriv (v t) (arcDeriv (v t) (q t)) x -
      2 * (P t x) ^ 2 + 2 * (q t x) ^ 2 + A * (q t x + Real.sqrt (q t x))

theorem contDiff_space_slice {f : ℝ → ℝ → ℝ} {U : Set ℝ} {t : ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ)) (ht : t ∈ U) :
    ContDiff ℝ ∞ (f t) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => ⟨ht, mem_univ x⟩)

theorem continuous_space_slice_of_strip {f : ℝ → ℝ → ℝ} {U : Set ℝ} {t : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ)) (ht : t ∈ U) :
    Continuous (f t) := by
  apply continuousOn_univ.mp
  exact hf.comp (continuousOn_const.prodMk continuousOn_id) (fun x _ => ⟨ht, mem_univ x⟩)

theorem periodic_deriv_one {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hp : Function.Periodic f 1) : Function.Periodic (deriv f) 1 := by
  intro x
  have he : (fun z => f (z + 1)) = f := funext hp
  have hd := (hf (x + 1)).hasDerivAt.comp x ((hasDerivAt_id x).add_const 1)
  dsimp only [Function.comp_def, id_eq] at hd
  rw [he] at hd
  simpa using hd.deriv.symm

theorem contDiff_arcDeriv {f v : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hvp : ∀ x, 0 < v x) :
    ContDiff ℝ ∞ (arcDeriv v f) :=
  (contDiff_infty_iff_deriv.mp hf).2.div hv (fun x => ne_of_gt (hvp x))

theorem ScalarCurveHypotheses.regularized_smooth
    {q v r P : ℝ → ℝ → ℝ} {a b A B ε : ℝ}
    (H : ScalarCurveHypotheses q v r P a b A B) (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => regularizedNorm (q p.1 p.2) ε)
      (Ioo a b ×ˢ univ) := by
  apply (H.q_smooth.add contDiffOn_const).sqrt
  intro p hp
  exact ne_of_gt (add_pos_of_nonneg_of_pos (H.q_nonneg p.1 (Ioo_subset_Icc_self hp.1) p.2)
    (sq_pos_of_pos hε))

theorem ScalarCurveHypotheses.length_hasDerivAt
    {q v r P : ℝ → ℝ → ℝ} {a b A B t : ℝ}
    (H : ScalarCurveHypotheses q v r P a b A B) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, v u x)
      (deriv (fun u => ∫ x in (0 : ℝ)..1, v u x) t) t := by
  have hd := hasDerivAt_weightedIntegral_of_contDiffOn
    (f := fun _ _ => 1) isOpen_Ioo ht contDiffOn_const (H.v_smooth.of_le (by simp))
  simpa only [one_mul] using hd.differentiableAt.hasDerivAt

theorem ScalarCurveHypotheses.length_deriv_le
    {q v r P : ℝ → ℝ → ℝ} {a b A B t : ℝ}
    (H : ScalarCurveHypotheses q v r P a b A B) (ht : t ∈ Ioo a b) :
    deriv (fun u => ∫ x in (0 : ℝ)..1, v u x) t ≤
      B * (∫ x in (0 : ℝ)..1, v t x) := by
  have hti := Ioo_subset_Icc_self ht
  have qcont := (contDiff_space_slice H.q_smooth ht).continuous
  have vcont := (contDiff_space_slice H.v_smooth ht).continuous
  have dtcont := continuous_space_slice_of_strip
    (f := fun u x => deriv (fun z => v z x) u)
    (continuousOn_time_deriv_of_contDiffOn isOpen_Ioo (H.v_smooth.of_le (by simp))) ht
  have il : IntervalIntegrable (fun x => -(q t x + r t x) * v t x) volume 0 1 := by
    rw [← funext (H.density_evolution t ht)]
    exact dtcont.intervalIntegrable _ _
  have D : MovingWeightData (fun _ _ => 1) v (fun _ _ => 0)
      (fun u x => deriv (fun z => v z x) u) t := by
    simpa only [deriv_const] using
      movingWeightData_of_contDiffOn (f := fun _ _ => 1) isOpen_Ioo ht contDiffOn_const
        (H.v_smooth.of_le (by simp))
  have h := deriv_length_le (vt := fun u x => deriv (fun z => v z x) u) D
    (fun x _ => H.density_evolution t ht x)
    (fun x _ => (H.v_pos t hti x).le) (fun x _ => H.ricci_bound t ht x)
    il (vcont.intervalIntegrable _ _) ((qcont.mul vcont).intervalIntegrable _ _)
  have he : 0 ≤ ∫ x in (0 : ℝ)..1, q t x * v t x :=
    intervalIntegral.integral_nonneg zero_le_one
      (fun x _ => mul_nonneg (H.q_nonneg t hti x) (H.v_pos t hti x).le)
  linarith

theorem ScalarCurveHypotheses.regularized_deriv_le
    {q v r P : ℝ → ℝ → ℝ} {a b A B t ε : ℝ}
    (H : ScalarCurveHypotheses q v r P a b A B) (ht : t ∈ Ioo a b) (hε : 0 < ε) :
    deriv (fun u => regularizedWeightedCurvature (q u) (v u) ε) t ≤
      (A / 2 + B) * regularizedWeightedCurvature (q t) (v t) ε +
      (A / 2) * (∫ x in (0 : ℝ)..1, v t x) := by
  let h : ℝ → ℝ → ℝ := fun u x => regularizedNorm (q u x) ε
  have hti := Ioo_subset_Icc_self ht
  have qs := contDiff_space_slice H.q_smooth ht
  have vs := contDiff_space_slice H.v_smooth ht
  have hs : ContDiffOn ℝ ∞ (Function.uncurry h) (Ioo a b ×ˢ univ) := H.regularized_smooth hε
  have hspace := contDiff_space_slice hs ht
  have haspace := contDiff_arcDeriv hspace vs (H.v_pos t hti)
  have hasspace := contDiff_arcDeriv haspace vs (H.v_pos t hti)
  have htcont := continuous_space_slice_of_strip
    (f := fun u x => deriv (fun z => h z x) u)
    (continuousOn_time_deriv_of_contDiffOn isOpen_Ioo (hs.of_le (by simp))) ht
  have vtcont := continuous_space_slice_of_strip
    (f := fun u x => deriv (fun z => v z x) u)
    (continuousOn_time_deriv_of_contDiffOn isOpen_Ioo (H.v_smooth.of_le (by simp))) ht
  have ileft : IntervalIntegrable
      (fun x => (deriv (fun z => h z x) t - h t x * (q t x + r t x)) * v t x) volume 0 1 := by
    have he : (fun x => (deriv (fun z => h z x) t - h t x * (q t x + r t x)) * v t x) =
        (fun x => deriv (fun z => h z x) t * v t x + h t x * deriv (fun z => v z x) t) := by
      funext x
      rw [H.density_evolution t ht x]
      ring
    rw [he]
    exact ((htcont.mul vs.continuous).add (hspace.continuous.mul vtcont)).intervalIntegrable _ _
  have hp : Function.Periodic (h t) 1 := by
    intro x
    dsimp [h]
    rw [H.q_periodic t ht x]
  have hap : arcDeriv (v t) (h t) 1 = arcDeriv (v t) (h t) 0 := by
    have hp' := periodic_deriv_one (hspace.differentiable (by simp)) hp 0
    have vp' := H.v_periodic t ht 0
    simpa [arcDeriv] using congrArg₂ (fun x y : ℝ => x / y) hp' vp'
  apply deriv_regularizedTotal_le
    (movingWeightData_of_contDiffOn isOpen_Ioo ht (hs.of_le (by simp))
      (H.v_smooth.of_le (by simp)))
    (fun x _ => H.density_evolution t ht x)
    (fun x _ => H.q_nonneg t hti x) (fun x _ => H.v_pos t hti x)
    (fun x _ => H.ricci_bound t ht x)
  · intro x _
    exact deriv_regularizedNorm_le
      (hasDerivAt_time_slice_of_contDiffOn isOpen_Ioo (H.q_smooth.of_le (by simp))
        (x := x) ht).differentiableAt
      (qs.differentiable (by simp))
      ((contDiff_infty_iff_deriv.mp qs).2.differentiable (by simp) x)
      (vs.differentiable (by simp) x) (H.v_pos t hti x) (H.q_nonneg t hti)
      hε H.A_nonneg (H.kato t ht x) (H.squared_pde t ht x)
  · exact ileft
  · exact (hasspace.continuous.mul vs.continuous).intervalIntegrable _ _
  · exact (hspace.continuous.mul vs.continuous).intervalIntegrable _ _
  · exact vs.continuous.intervalIntegrable _ _
  · exact fun x _ => haspace.differentiable (by simp) x
  · exact (haspace.continuous_deriv (by simp)).intervalIntegrable _ _
  · exact hap

theorem ScalarCurveHypotheses.regularized_comparison
    {q v r P : ℝ → ℝ → ℝ} {a b A B ε : ℝ}
    (H : ScalarCurveHypotheses q v r P a b A B) (hε : 0 < ε) :
    ∀ t ∈ Icc a b,
      (∫ x in (0 : ℝ)..1, v t x) ≤
        (∫ x in (0 : ℝ)..1, v a x) * Real.exp (B * (t - a)) ∧
      regularizedWeightedCurvature (q t) (v t) ε + (∫ x in (0 : ℝ)..1, v t x) ≤
        (regularizedWeightedCurvature (q a) (v a) ε + (∫ x in (0 : ℝ)..1, v a x)) *
          Real.exp ((A / 2 + B) * (t - a)) := by
  let L : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..1, v u x
  let Q : ℝ → ℝ := fun u => regularizedWeightedCurvature (q u) (v u) ε
  have hcL : ContinuousOn L (Icc a b) := by
    simpa only [one_mul] using continuousOn_weightedIntegral_of_rectangle
      (f := fun _ _ => 1) continuousOn_const H.v_continuous
  have hcQ : ContinuousOn Q (Icc a b) :=
    continuousOn_weightedIntegral_of_rectangle
      (f := fun u x => regularizedNorm (q u x) ε)
      (H.q_continuous.add continuousOn_const).sqrt H.v_continuous
  apply coupled_exp_comparison_interior_on (L := L) (Q := Q)
    (L' := deriv L) (Q' := deriv Q) hcL hcQ
  · intro t ht
    exact (H.length_hasDerivAt ht).hasDerivWithinAt
  · intro t ht
    exact (hasDerivAt_weightedIntegral_of_contDiffOn isOpen_Ioo ht
      ((H.regularized_smooth hε).of_le (by simp))
      (H.v_smooth.of_le (by simp))).differentiableAt.hasDerivAt.hasDerivWithinAt
  · exact fun t ht => H.length_deriv_le ht
  · exact fun t ht => H.regularized_deriv_le ht hε

/-- The complete scalar estimate, with a constant independent of the
regularization parameter. The initial time needs only rectangle continuity.
Here `weightedCurvature (q t) (v t)` is the actual integral `∫₀¹ √q v`. -/
theorem ScalarCurveHypotheses.curve_estimate
    {q v r P : ℝ → ℝ → ℝ} {a b A B : ℝ}
    (H : ScalarCurveHypotheses q v r P a b A B) :
    ∀ t ∈ Icc a b,
      (∫ x in (0 : ℝ)..1, v t x) ≤
        (∫ x in (0 : ℝ)..1, v a x) * Real.exp (B * (t - a)) ∧
      weightedCurvature (q t) (v t) + (∫ x in (0 : ℝ)..1, v t x) ≤
        (weightedCurvature (q a) (v a) + (∫ x in (0 : ℝ)..1, v a x)) *
          Real.exp ((A / 2 + B) * (t - a)) := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  constructor
  · exact (H.regularized_comparison (ε := 1) zero_lt_one t ht).1
  · apply weightedCurvature_exp_bound
      (continuousOn_space_slice H.q_continuous ht)
      (continuousOn_space_slice H.v_continuous ht)
      (fun x _ => H.q_nonneg t ht x) (fun x _ => (H.v_pos t ht x).le)
      (continuousOn_space_slice H.q_continuous ha)
      (continuousOn_space_slice H.v_continuous ha)
      (fun x _ => H.q_nonneg a ha x) (fun x _ => (H.v_pos a ha x).le)
    exact fun ε hε => (H.regularized_comparison hε t ht).2

end CurveControl.Analysis

#print axioms CurveControl.Analysis.ScalarCurveHypotheses
#print axioms CurveControl.Analysis.contDiff_space_slice
#print axioms CurveControl.Analysis.continuous_space_slice_of_strip
#print axioms CurveControl.Analysis.periodic_deriv_one
#print axioms CurveControl.Analysis.contDiff_arcDeriv
#print axioms CurveControl.Analysis.ScalarCurveHypotheses.regularized_smooth
#print axioms CurveControl.Analysis.ScalarCurveHypotheses.length_hasDerivAt
#print axioms CurveControl.Analysis.ScalarCurveHypotheses.length_deriv_le
#print axioms CurveControl.Analysis.ScalarCurveHypotheses.regularized_deriv_le
#print axioms CurveControl.Analysis.ScalarCurveHypotheses.regularized_comparison
#print axioms CurveControl.Analysis.ScalarCurveHypotheses.curve_estimate
