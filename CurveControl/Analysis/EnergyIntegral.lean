import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Abstract energy integral comparison

These are scalar analysis lemmas, not curve-flow evolution theorems. The geometric
caller must prove the length differential inequality and identify its energy.
Only continuity of length on the closed interval and actual right derivatives in
its interior are required. There is no assumption of endpoint differentiability
or integrability of the length derivative. Energy need only be integrable.
-/

open Set Real MeasureTheory

namespace CurveControl.Analysis

/-- Integrating-factor energy estimate. The right derivative is needed only in
the open interval. This weighted estimate does not require sign assumptions. -/
theorem weighted_energy_integral_le
    {L L' E : ℝ → ℝ} {s t B : ℝ}
    (hst : s ≤ t) (hL : ContinuousOn L (Icc s t))
    (hL' : ∀ r ∈ Ioo s t, HasDerivWithinAt L (L' r) (Ioi r) r)
    (hE : IntegrableOn E (Icc s t))
    (hbound : ∀ r ∈ Ioo s t, L' r ≤ B * L r - E r) :
    (∫ r in s..t, exp (-B * (r - s)) * E r) ≤
      L s - exp (-B * (t - s)) * L t := by
  let w : ℝ → ℝ := fun r => exp (-B * (r - s))
  have hw : ∀ r, HasDerivAt w (-B * w r) r := by
    intro r
    convert (((hasDerivAt_id r).sub_const s).const_mul (-B)).exp using 1 <;>
      simp [w, mul_comm]
  have hwcont : ContinuousOn w (Icc s t) :=
    (continuous_iff_continuousAt.mpr fun r => (hw r).continuousAt).continuousOn
  have hWE : IntegrableOn (fun r => w r * E r) (Icc s t) :=
    hE.continuousOn_mul hwcont isCompact_Icc
  have hd : ∀ r ∈ Ioo s t,
      HasDerivWithinAt (fun x => -(w x * L x))
        (w r * (B * L r - L' r)) (Ioi r) r := by
    intro r hr
    have hd0 : HasDerivWithinAt (fun x => -(w x * L x))
        (-((-B * w r) * L r + w r * L' r)) (Ioi r) r :=
      ((hw r).hasDerivWithinAt.mul (hL' r hr)).neg
    convert hd0 using 1
    ring
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hst
    (hwcont.mul hL).neg hd hWE (fun r hr =>
      mul_le_mul_of_nonneg_left (by linarith [hbound r hr]) (exp_pos _).le)
  dsimp [w] at h
  simp only [sub_self, mul_zero, exp_zero, one_mul] at h
  linarith

/-- For nonnegative energy and nonnegative growth coefficient, the weighted
estimate gives the unweighted accumulated-energy bound. Length itself need not
be assumed nonnegative in this abstract implication. -/
theorem energy_integral_le
    {L L' E : ℝ → ℝ} {s t B : ℝ}
    (hst : s ≤ t) (hL : ContinuousOn L (Icc s t))
    (hL' : ∀ r ∈ Ioo s t, HasDerivWithinAt L (L' r) (Ioi r) r)
    (hE : IntegrableOn E (Icc s t))
    (hbound : ∀ r ∈ Ioo s t, L' r ≤ B * L r - E r)
    (hB : 0 ≤ B) (hEpos : ∀ r ∈ Icc s t, 0 ≤ E r) :
    (∫ r in s..t, E r) ≤ exp (B * (t - s)) * L s - L t := by
  have hwcont : ContinuousOn (fun r => exp (-B * (r - s))) (Icc s t) := by
    fun_prop
  have hWE := hE.continuousOn_mul hwcont isCompact_Icc
  have hEi : IntervalIntegrable E volume s t := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr hE
  have hWEi : IntervalIntegrable (fun r => exp (-B * (r - s)) * E r) volume s t := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr hWE
  have hcompare : (∫ r in s..t, E r) ≤
      exp (B * (t - s)) * (∫ r in s..t, exp (-B * (r - s)) * E r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hst hEi (hWEi.const_mul _)
    intro r hr
    have he : 1 ≤ exp (B * (t - s)) * exp (-B * (r - s)) := by
      rw [← exp_add, one_le_exp_iff]
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hr.2)]
    calc
      E r = 1 * E r := (one_mul _).symm
      _ ≤ (exp (B * (t - s)) * exp (-B * (r - s))) * E r :=
        mul_le_mul_of_nonneg_right he (hEpos r hr)
      _ = exp (B * (t - s)) * (exp (-B * (r - s)) * E r) := mul_assoc _ _ _
  have hweighted := weighted_energy_integral_le hst hL hL' hE hbound
  have hexp : exp (B * (t - s)) * exp (-B * (t - s)) = 1 := by
    rw [← exp_add]
    have hz : B * (t - s) + -B * (t - s) = 0 := by ring
    rw [hz, exp_zero]
  calc
    (∫ r in s..t, E r) ≤
        exp (B * (t - s)) * (∫ r in s..t, exp (-B * (r - s)) * E r) := hcompare
    _ ≤ exp (B * (t - s)) * (L s - exp (-B * (t - s)) * L t) :=
      mul_le_mul_of_nonneg_left hweighted (exp_pos _).le
    _ = exp (B * (t - s)) * L s - L t := by rw [mul_sub, ← mul_assoc, hexp, one_mul]

end CurveControl.Analysis

#print axioms CurveControl.Analysis.weighted_energy_integral_le
#print axioms CurveControl.Analysis.energy_integral_le
