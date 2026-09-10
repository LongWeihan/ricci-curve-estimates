import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absorbing the corrected curvature error

This is the scalar contraction estimate for the spatial-connection version of
the correction to Section 19.2. The geometric caller must supply bounds on the
actual Ricci, curvature and covariant-Ricci contractions. These assumptions are
not a substitute for proving their occurrence in the geometric evolution law.
-/

namespace CurveControl.Analysis

/-- A single coefficient controlling the quadratic and linear curvature errors. -/
def curvatureErrorCoefficient (B K D : ℝ) : ℝ := max (6 * B + 2 * K) (6 * D)

theorem curvatureErrorCoefficient_nonneg {B K D : ℝ} (hD : 0 ≤ D) :
    0 ≤ curvatureErrorCoefficient B K D :=
  le_trans (by linarith) (le_max_right _ _)

/-- The correction terms are bounded by a quadratic and a linear term. -/
theorem corrected_curvature_error_le
    {k B K D rSS rHH rHSHS dSSH dHSS : ℝ}
    (hk : 0 ≤ k)
    (hSS : |rSS| ≤ B) (hHH : |rHH| ≤ B * k ^ 2)
    (hRm : |rHSHS| ≤ K * k ^ 2)
    (hDS : |dSSH| ≤ D * k) (hDH : |dHSS| ≤ D * k) :
    4 * k ^ 2 * rSS - 2 * rHH + 2 * rHSHS - 4 * dSSH + 2 * dHSS ≤
      (6 * B + 2 * K) * k ^ 2 + 6 * D * k := by
  have hSS' := (abs_le.mp hSS).2
  have hHH' := (abs_le.mp hHH).1
  have hRm' := (abs_le.mp hRm).2
  have hDS' := (abs_le.mp hDS).1
  have hDH' := (abs_le.mp hDH).2
  have hprod := mul_le_mul_of_nonneg_left hSS' (sq_nonneg k)
  nlinarith

theorem corrected_curvature_error_abs_le
    {k B K D rSS rHH rHSHS dSSH dHSS : ℝ}
    (hk : 0 ≤ k)
    (hSS : |rSS| ≤ B) (hHH : |rHH| ≤ B * k ^ 2)
    (hRm : |rHSHS| ≤ K * k ^ 2)
    (hDS : |dSSH| ≤ D * k) (hDH : |dHSS| ≤ D * k) :
    |4 * k ^ 2 * rSS - 2 * rHH + 2 * rHSHS - 4 * dSSH + 2 * dHSS| ≤
      (6 * B + 2 * K) * k ^ 2 + 6 * D * k := by
  apply abs_le.mpr
  constructor
  · have h := corrected_curvature_error_le (rSS := -rSS) (rHH := -rHH)
      (rHSHS := -rHSHS) (dSSH := -dSSH) (dHSS := -dHSS) hk
      (by simpa using hSS) (by simpa using hHH) (by simpa using hRm)
      (by simpa using hDS) (by simpa using hDH)
    linarith
  · exact corrected_curvature_error_le hk hSS hHH hRm hDS hDH

theorem corrected_curvature_error_le_coefficient
    {k B K D rSS rHH rHSHS dSSH dHSS : ℝ}
    (hk : 0 ≤ k)
    (hSS : |rSS| ≤ B) (hHH : |rHH| ≤ B * k ^ 2)
    (hRm : |rHSHS| ≤ K * k ^ 2)
    (hDS : |dSSH| ≤ D * k) (hDH : |dHSS| ≤ D * k) :
    4 * k ^ 2 * rSS - 2 * rHH + 2 * rHSHS - 4 * dSSH + 2 * dHSS ≤
      curvatureErrorCoefficient B K D * (k ^ 2 + k) := by
  apply (corrected_curvature_error_le hk hSS hHH hRm hDS hDH).trans
  have hq := mul_le_mul_of_nonneg_right (le_max_left (6 * B + 2 * K) (6 * D))
    (sq_nonneg k)
  have hl := mul_le_mul_of_nonneg_right (le_max_right (6 * B + 2 * K) (6 * D)) hk
  dsimp [curvatureErrorCoefficient]
  nlinarith

end CurveControl.Analysis
