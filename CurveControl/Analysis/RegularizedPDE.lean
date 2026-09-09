import CurveControl.Analysis.RegularizedNorm
import CurveControl.Analysis.WeightedIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

/-!
# Scalar regularization of a supplied squared-curvature inequality

The spatial chain rules are proved using actual derivatives. The Kato bound
and squared-curvature evolution inequality in the later theorems are explicit
inputs for the geometry layer to prove, not asserted geometric conclusions.
-/

namespace CurveControl.Analysis

theorem arcDeriv_regularizedNorm {q v : ℝ → ℝ} {x ε : ℝ}
    (hq : DifferentiableAt ℝ q x) (hq0 : 0 ≤ q x) (hε : 0 < ε) :
    arcDeriv v (fun y => regularizedNorm (q y) ε) x =
      arcDeriv v q x / (2 * regularizedNorm (q x) ε) := by
  unfold arcDeriv
  rw [(hasDerivAt_regularizedNorm hq.hasDerivAt hq0 hε).deriv]
  exact div_right_comm _ _ _

/-- The hypotheses are weaker than global `C²` regularity of `q` and `C¹`
regularity of `v`: only the stated pointwise derivatives are needed. -/
theorem arcDeriv_arcDeriv_regularizedNorm {q v : ℝ → ℝ} {x ε : ℝ}
    (hq : Differentiable ℝ q) (hq2 : DifferentiableAt ℝ (deriv q) x)
    (hv : DifferentiableAt ℝ v x) (hv0 : 0 < v x)
    (hq0 : ∀ y, 0 ≤ q y) (hε : 0 < ε) :
    arcDeriv v (arcDeriv v (fun y => regularizedNorm (q y) ε)) x =
      arcDeriv v (arcDeriv v q) x / (2 * regularizedNorm (q x) ε) -
        (arcDeriv v q x) ^ 2 / (4 * regularizedNorm (q x) ε ^ 3) := by
  have heq : arcDeriv v (fun y => regularizedNorm (q y) ε) =
      fun y => arcDeriv v q y / (2 * regularizedNorm (q y) ε) :=
    funext fun y => arcDeriv_regularizedNorm (hq y) (hq0 y) hε
  have hh := hasDerivAt_regularizedNorm (hq x).hasDerivAt (hq0 x) hε
  have hp : DifferentiableAt ℝ (arcDeriv v q) x := hq2.div hv (ne_of_gt hv0)
  have hn := ne_of_gt (regularizedNorm_pos (hq0 x) hε)
  have hd := hp.hasDerivAt.div (hh.const_mul 2) (mul_ne_zero (by norm_num) hn)
  rw [heq]
  unfold arcDeriv at *
  have hde := hd.deriv
  change deriv (fun y => deriv q y / v y / (2 * regularizedNorm (q y) ε)) x = _ at hde
  rw [hde]
  field_simp
  ring

/-- Cancellation of the negative gradient term after regularization. The
gradient inequality is supplied by a separate geometric Kato proof. -/
theorem regularized_kato_cancellation {q qs P ε : ℝ}
    (hq : 0 ≤ q) (hε : 0 < ε) (hK : qs ^ 2 ≤ 4 * q * P ^ 2) :
    qs ^ 2 / (4 * regularizedNorm q ε ^ 3) ≤ P ^ 2 / regularizedNorm q ε := by
  have hp := regularizedNorm_pos hq hε
  have hn := ne_of_gt hp
  have hqle : q ≤ regularizedNorm q ε ^ 2 := by
    nlinarith [regularizedNorm_sq (ε := ε) hq, sq_nonneg ε]
  have hm := mul_le_mul_of_nonneg_right hqle (sq_nonneg P)
  apply (div_le_iff₀ (mul_pos (by norm_num) (pow_pos hp 3))).2
  have heq : P ^ 2 / regularizedNorm q ε * (4 * regularizedNorm q ε ^ 3) =
      4 * regularizedNorm q ε ^ 2 * P ^ 2 := by field_simp
  rw [heq]
  nlinarith

/-- Pure scalar consequence of the explicitly supplied evolution and Kato
inequalities. Here `qt`, `qs`, `qss` are scalar slots, not hidden derivatives. -/
theorem regularized_pde_algebra {q qt qs qss P A ε : ℝ}
    (hq : 0 ≤ q) (hε : 0 < ε) (hA : 0 ≤ A)
    (hK : qs ^ 2 ≤ 4 * q * P ^ 2)
    (hPDE : qt ≤ qss - 2 * P ^ 2 + 2 * q ^ 2 + A * (q + Real.sqrt q)) :
    qt / (2 * regularizedNorm q ε) ≤
      qss / (2 * regularizedNorm q ε) - qs ^ 2 / (4 * regularizedNorm q ε ^ 3) +
        (Real.sqrt q) ^ 3 + (A / 2) * (regularizedNorm q ε + 1) := by
  have hp := regularizedNorm_pos hq hε
  have hn := ne_of_gt hp
  have hd := div_le_div_of_nonneg_right hPDE
    (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hp))
  have heq : (qss - 2 * P ^ 2 + 2 * q ^ 2 + A * (q + Real.sqrt q)) /
      (2 * regularizedNorm q ε) =
      qss / (2 * regularizedNorm q ε) - P ^ 2 / regularizedNorm q ε +
        q ^ 2 / regularizedNorm q ε +
          (A / 2) * (q / regularizedNorm q ε + Real.sqrt q / regularizedNorm q ε) := by
    field_simp
  rw [heq] at hd
  have hterm := mul_le_mul_of_nonneg_left
    (add_le_add (div_regularizedNorm_le hq hε) (sqrt_div_regularizedNorm_le_one hq hε))
    (show 0 ≤ A / 2 from div_nonneg hA (by norm_num))
  linarith [regularized_kato_cancellation hq hε hK,
    sq_div_regularizedNorm_le_sqrt_cube hq hε]

/-- Actual time differentiation followed by the scalar comparison. The
spatial chain rule is already proved above; the PDE and Kato inputs must be
discharged by the geometry layer. -/
theorem deriv_regularizedNorm_le {q : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {t x ε P A : ℝ}
    (hqt : DifferentiableAt ℝ (fun u => q u x) t)
    (hq : Differentiable ℝ (q t)) (hq2 : DifferentiableAt ℝ (deriv (q t)) x)
    (hv : DifferentiableAt ℝ v x) (hv0 : 0 < v x)
    (hq0 : ∀ y, 0 ≤ q t y) (hε : 0 < ε) (hA : 0 ≤ A)
    (hK : (arcDeriv v (q t) x) ^ 2 ≤ 4 * q t x * P ^ 2)
    (hPDE : deriv (fun u => q u x) t ≤ arcDeriv v (arcDeriv v (q t)) x -
      2 * P ^ 2 + 2 * (q t x) ^ 2 + A * (q t x + Real.sqrt (q t x))) :
    deriv (fun u => regularizedNorm (q u x) ε) t ≤
      arcDeriv v (arcDeriv v (fun y => regularizedNorm (q t y) ε)) x +
        (Real.sqrt (q t x)) ^ 3 + (A / 2) * (regularizedNorm (q t x) ε + 1) := by
  rw [(hasDerivAt_regularizedNorm hqt.hasDerivAt (hq0 x) hε).deriv,
    arcDeriv_arcDeriv_regularizedNorm hq hq2 hv hv0 hq0 hε]
  exact regularized_pde_algebra (hq0 x) hε hA hK hPDE

end CurveControl.Analysis
