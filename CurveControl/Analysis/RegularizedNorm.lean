import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar regularization at zero curvature

The regularization of a squared norm `q` is `sqrt (q + ε²)`.
These scalar lemmas do not assume or assert a geometric evolution equation.
-/

namespace CurveControl

noncomputable def regularizedNorm (q ε : ℝ) : ℝ := Real.sqrt (q + ε ^ 2)

theorem regularizedNorm_nonneg (q ε : ℝ) : 0 ≤ regularizedNorm q ε :=
  Real.sqrt_nonneg _

theorem regularizedNorm_pos {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) :
    0 < regularizedNorm q ε := by
  apply Real.sqrt_pos.2
  exact add_pos_of_nonneg_of_pos hq (sq_pos_of_pos hε)

theorem regularizedNorm_sq {q ε : ℝ} (hq : 0 ≤ q) :
    regularizedNorm q ε ^ 2 = q + ε ^ 2 :=
  Real.sq_sqrt (add_nonneg hq (sq_nonneg ε))

theorem sqrt_le_regularizedNorm (q ε : ℝ) :
    Real.sqrt q ≤ regularizedNorm q ε :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))

theorem regularizedNorm_le_sqrt_add {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    regularizedNorm q ε ≤ Real.sqrt q + ε := by
  have hs := Real.sq_sqrt hq
  have hr := regularizedNorm_sq (ε := ε) hq
  have hn := regularizedNorm_nonneg q ε
  have ht := Real.sqrt_nonneg q
  nlinarith [mul_nonneg ht hε]

theorem regularizedNorm_sub_sqrt_bounds {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    0 ≤ regularizedNorm q ε - Real.sqrt q ∧
      regularizedNorm q ε - Real.sqrt q ≤ ε := by
  constructor
  · exact sub_nonneg.mpr (sqrt_le_regularizedNorm q ε)
  · exact sub_le_iff_le_add.mpr (by simpa [add_comm] using regularizedNorm_le_sqrt_add hq hε)

theorem sq_div_regularizedNorm_le_sqrt_cube {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) :
    q ^ 2 / regularizedNorm q ε ≤ (Real.sqrt q) ^ 3 := by
  apply (div_le_iff₀ (regularizedNorm_pos hq hε)).2
  have hs := Real.sq_sqrt hq
  have hm := mul_le_mul_of_nonneg_left (sqrt_le_regularizedNorm q ε)
    (pow_nonneg (Real.sqrt_nonneg q) 3)
  calc
    q ^ 2 = ((Real.sqrt q) ^ 2) ^ 2 := by rw [hs]
    _ = (Real.sqrt q) ^ 3 * Real.sqrt q := by ring
    _ ≤ (Real.sqrt q) ^ 3 * regularizedNorm q ε := hm

theorem div_regularizedNorm_le {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) :
    q / regularizedNorm q ε ≤ regularizedNorm q ε := by
  apply (div_le_iff₀ (regularizedNorm_pos hq hε)).2
  nlinarith [regularizedNorm_sq (ε := ε) hq, sq_nonneg ε]

theorem sqrt_div_regularizedNorm_le_one {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) :
    Real.sqrt q / regularizedNorm q ε ≤ 1 := by
  apply (div_le_iff₀ (regularizedNorm_pos hq hε)).2
  simpa using sqrt_le_regularizedNorm q ε

theorem hasDerivAt_regularizedNorm {q : ℝ → ℝ} {q' t ε : ℝ}
    (hd : HasDerivAt q q' t) (hq : 0 ≤ q t) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedNorm (q s) ε)
      (q' / (2 * regularizedNorm (q t) ε)) t := by
  have ha : HasDerivAt (fun s => q s + ε ^ 2) q' t := hd.add_const (ε ^ 2)
  exact ha.sqrt
    (ne_of_gt (add_pos_of_nonneg_of_pos hq (sq_pos_of_pos hε)))

theorem continuous_regularizedNorm_parameter (q : ℝ) :
    Continuous (regularizedNorm q) :=
  (continuous_const.add (continuous_id.pow 2)).sqrt

theorem tendsto_regularizedNorm_zero (q : ℝ) :
    Filter.Tendsto (regularizedNorm q) (nhds 0) (nhds (Real.sqrt q)) := by
  simpa [regularizedNorm] using (continuous_regularizedNorm_parameter q).tendsto 0

theorem abs_regularizedNorm_sub_sqrt_le {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    |regularizedNorm q ε - Real.sqrt q| ≤ ε := by
  obtain ⟨hl, hu⟩ := regularizedNorm_sub_sqrt_bounds hq hε
  simpa [abs_of_nonneg hl] using hu

theorem tendsto_regularizedNorm_error_zero (q : ℝ) :
    Filter.Tendsto (fun ε => regularizedNorm q ε - Real.sqrt q)
      (nhds 0) (nhds 0) := by
  simpa using (tendsto_regularizedNorm_zero q).sub (tendsto_const_nhds (x := Real.sqrt q))

end CurveControl
