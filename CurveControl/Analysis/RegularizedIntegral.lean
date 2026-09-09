import CurveControl.Analysis.RegularizedNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Removing scalar regularization after integral comparison

The functions here are actual continuous squared norms and nonnegative density
functions on `[0,1]`. No geometric evolution law is assumed. The exponential
comparison is passed to the limit only after it has been established for each
positive regularization parameter; no derivative is interchanged with a limit.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace CurveControl

noncomputable def weightedCurvature (q v : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.sqrt (q s) * v s

noncomputable def regularizedWeightedCurvature (q v : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, regularizedNorm (q s) ε * v s

theorem regularizedWeightedCurvature_sub_bounds {q v : ℝ → ℝ} {ε : ℝ}
    (hq : ContinuousOn q (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hq0 : ∀ s ∈ Icc 0 1, 0 ≤ q s) (hv0 : ∀ s ∈ Icc 0 1, 0 ≤ v s)
    (hε : 0 ≤ ε) :
    0 ≤ regularizedWeightedCurvature q v ε - weightedCurvature q v ∧
      regularizedWeightedCurvature q v ε - weightedCurvature q v ≤
        ε * ∫ s in (0 : ℝ)..1, v s := by
  have hc : ContinuousOn (fun s => regularizedNorm (q s) ε) (Icc 0 1) :=
    (hq.add continuousOn_const).sqrt
  have hi : IntervalIntegrable (fun s => regularizedNorm (q s) ε * v s) volume 0 1 :=
    (hc.mul hv).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hj : IntervalIntegrable (fun s => Real.sqrt (q s) * v s) volume 0 1 :=
    (hq.sqrt.mul hv).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hk : IntervalIntegrable (fun s => ε * v s) volume 0 1 :=
    (continuousOn_const.mul hv).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1)
  have heq : regularizedWeightedCurvature q v ε - weightedCurvature q v =
      ∫ s in (0 : ℝ)..1, (regularizedNorm (q s) ε * v s - Real.sqrt (q s) * v s) :=
    (intervalIntegral.integral_sub hi hj).symm
  rw [heq]
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro s hs
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right (sqrt_le_regularizedNorm _ _) (hv0 s hs))
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num) (hi.sub hj) hk
    intro s hs
    have h := mul_le_mul_of_nonneg_right
      (regularizedNorm_sub_sqrt_bounds (hq0 s hs) hε).2 (hv0 s hs)
    simpa only [sub_mul] using h

theorem tendsto_regularizedWeightedCurvature {q v : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hq0 : ∀ s ∈ Icc 0 1, 0 ≤ q s) (hv0 : ∀ s ∈ Icc 0 1, 0 ≤ v s) :
    Tendsto (regularizedWeightedCurvature q v) (𝓝[>] 0) (𝓝 (weightedCurvature q v)) := by
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 ≤ regularizedWeightedCurvature q v ε - weightedCurvature q v ∧
        regularizedWeightedCurvature q v ε - weightedCurvature q v ≤
          ε * ∫ s in (0 : ℝ)..1, v s :=
    Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0) fun ε hε =>
      regularizedWeightedCurvature_sub_bounds hq hv hq0 hv0 (le_of_lt hε)
  have hu : Tendsto (fun ε : ℝ => ε * ∫ s in (0 : ℝ)..1, v s) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.mul_const (∫ s in (0 : ℝ)..1, v s)
  have he : Tendsto (fun ε => regularizedWeightedCurvature q v ε - weightedCurvature q v)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
  simpa using he.add_const (weightedCurvature q v)

/-- Transfer a previously proved regularized exponential comparison to its limits. -/
theorem exp_bound_of_regularized_limits {A B : ℝ → ℝ} {a b L L₀ C t : ℝ}
    (hA : Tendsto A (𝓝[>] 0) (𝓝 a)) (hB : Tendsto B (𝓝[>] 0) (𝓝 b))
    (hbound : ∀ ε > 0, A ε + L ≤ (B ε + L₀) * Real.exp (C * t)) :
    a + L ≤ (b + L₀) * Real.exp (C * t) := by
  apply le_of_tendsto_of_tendsto (hA.add_const L)
    ((hB.add_const L₀).mul_const (Real.exp (C * t)))
  exact Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0) fun ε hε => hbound ε hε

theorem weightedCurvature_exp_bound {q v q₀ v₀ : ℝ → ℝ} {C t : ℝ}
    (hq : ContinuousOn q (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hq0 : ∀ s ∈ Icc 0 1, 0 ≤ q s) (hv0 : ∀ s ∈ Icc 0 1, 0 ≤ v s)
    (hq₀ : ContinuousOn q₀ (Icc 0 1)) (hv₀ : ContinuousOn v₀ (Icc 0 1))
    (hq₀0 : ∀ s ∈ Icc 0 1, 0 ≤ q₀ s) (hv₀0 : ∀ s ∈ Icc 0 1, 0 ≤ v₀ s)
    (hbound : ∀ ε > 0,
      regularizedWeightedCurvature q v ε + (∫ s in (0 : ℝ)..1, v s) ≤
        (regularizedWeightedCurvature q₀ v₀ ε + (∫ s in (0 : ℝ)..1, v₀ s)) * Real.exp (C * t)) :
    weightedCurvature q v + (∫ s in (0 : ℝ)..1, v s) ≤
      (weightedCurvature q₀ v₀ + (∫ s in (0 : ℝ)..1, v₀ s)) * Real.exp (C * t) :=
  exp_bound_of_regularized_limits (tendsto_regularizedWeightedCurvature hq hv hq0 hv0)
    (tendsto_regularizedWeightedCurvature hq₀ hv₀ hq₀0 hv₀0) hbound

end CurveControl
