import Mathlib.Analysis.ODE.Gronwall

/-!
# Abstract coupled exponential comparison

This file adapts mathlib's Grönwall comparison engine to the two scalar quantities
used for length and regularized total curvature. It is an analysis component only:
the geometric application must prove continuity, the indicated right derivatives,
and both differential inequalities from the geometric evolution equations.
In particular none of these hypotheses is a proved curve-flow evolution formula here.

The comparison works for arbitrary real coefficients and signed scalar functions.
The geometric assumptions `0 ≤ L` and `0 ≤ c₁` are therefore not needed at this
stage (they can be needed when deriving the differential inequalities).
-/

open Set Real

namespace CurveControl.Analysis

/-- Scalar exponential comparison, with a right derivative on the half-open time
interval. This is a specialization of mathlib's Grönwall engine, with zero forcing. -/
theorem le_exp_of_deriv_right_le
    {f f' : ℝ → ℝ} {a b K C : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hinit : f a ≤ C)
    (hbound : ∀ t ∈ Ico a b, f' t ≤ K * f t) :
    ∀ t ∈ Icc a b, f t ≤ C * exp (K * (t - a)) := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (ε := 0) hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) hinit
    (fun x hx => by simpa only [add_zero] using hbound x hx) t ht
  simpa only [gronwallBound_ε0] using h

/-- Coupled length/curvature comparison with their actual initial values.
All geometric differential inequalities remain explicit hypotheses; this theorem
does not assert that arbitrary curve flows satisfy them. -/
theorem coupled_exp_comparison_right
    {L Q L' Q' : ℝ → ℝ} {a b c₁ c₂ : ℝ}
    (hL : ContinuousOn L (Icc a b)) (hQ : ContinuousOn Q (Icc a b))
    (hL' : ∀ t ∈ Ico a b, HasDerivWithinAt L (L' t) (Ici t) t)
    (hQ' : ∀ t ∈ Ico a b, HasDerivWithinAt Q (Q' t) (Ici t) t)
    (hLbound : ∀ t ∈ Ico a b, L' t ≤ c₂ * L t)
    (hQbound : ∀ t ∈ Ico a b, Q' t ≤ (c₁ + c₂) * Q t + c₁ * L t) :
    ∀ t ∈ Icc a b,
      L t ≤ L a * exp (c₂ * (t - a)) ∧
      Q t + L t ≤ (Q a + L a) * exp ((c₁ + c₂) * (t - a)) := by
  have hsum : ∀ t ∈ Ico a b,
      Q' t + L' t ≤ (c₁ + c₂) * (Q t + L t) := by
    intro t ht
    calc
      Q' t + L' t ≤ ((c₁ + c₂) * Q t + c₁ * L t) + c₂ * L t :=
        add_le_add (hQbound t ht) (hLbound t ht)
      _ = (c₁ + c₂) * (Q t + L t) := by ring
  exact fun t ht =>
    ⟨le_exp_of_deriv_right_le hL hL' le_rfl hLbound t ht,
      le_exp_of_deriv_right_le (hQ.add hL)
        (fun x hx => (hQ' x hx).add (hL' x hx)) le_rfl hsum t ht⟩

/-- Classical-derivative interface to the coupled comparison. -/
theorem coupled_exp_comparison
    {L Q L' Q' : ℝ → ℝ} {a b c₁ c₂ : ℝ}
    (hL : ContinuousOn L (Icc a b)) (hQ : ContinuousOn Q (Icc a b))
    (hL' : ∀ t ∈ Ico a b, HasDerivAt L (L' t) t)
    (hQ' : ∀ t ∈ Ico a b, HasDerivAt Q (Q' t) t)
    (hLbound : ∀ t ∈ Ico a b, L' t ≤ c₂ * L t)
    (hQbound : ∀ t ∈ Ico a b, Q' t ≤ (c₁ + c₂) * Q t + c₁ * L t) :
    ∀ t ∈ Icc a b,
      L t ≤ L a * exp (c₂ * (t - a)) ∧
      Q t + L t ≤ (Q a + L a) * exp ((c₁ + c₂) * (t - a)) :=
  coupled_exp_comparison_right hL hQ
    (fun t ht => (hL' t ht).hasDerivWithinAt)
    (fun t ht => (hQ' t ht).hasDerivWithinAt) hLbound hQbound

/-- Arbitrary indexed families have the same exponential bounds whenever the
coefficients, initial time, and initial upper bounds are independent of the index.
No topology, finiteness, or compactness is imposed on the index type. -/
theorem family_coupled_exp_comparison_right
    {ι : Type*} {L Q L' Q' : ι → ℝ → ℝ} {a b c₁ c₂ Cₗ Cₛ : ℝ}
    (hL : ∀ i, ContinuousOn (L i) (Icc a b))
    (hQ : ∀ i, ContinuousOn (Q i) (Icc a b))
    (hL' : ∀ i t, t ∈ Ico a b → HasDerivWithinAt (L i) (L' i t) (Ici t) t)
    (hQ' : ∀ i t, t ∈ Ico a b → HasDerivWithinAt (Q i) (Q' i t) (Ici t) t)
    (hLbound : ∀ i t, t ∈ Ico a b → L' i t ≤ c₂ * L i t)
    (hQbound : ∀ i t, t ∈ Ico a b →
      Q' i t ≤ (c₁ + c₂) * Q i t + c₁ * L i t)
    (hLinit : ∀ i, L i a ≤ Cₗ)
    (hSumInit : ∀ i, Q i a + L i a ≤ Cₛ) :
    ∀ i t, t ∈ Icc a b →
      L i t ≤ Cₗ * exp (c₂ * (t - a)) ∧
      Q i t + L i t ≤ Cₛ * exp ((c₁ + c₂) * (t - a)) := by
  intro i t ht
  obtain ⟨hl, hs⟩ := coupled_exp_comparison_right (hL i) (hQ i)
    (hL' i) (hQ' i) (hLbound i) (hQbound i) t ht
  exact ⟨hl.trans (mul_le_mul_of_nonneg_right (hLinit i) (exp_pos _).le),
    hs.trans (mul_le_mul_of_nonneg_right (hSumInit i) (exp_pos _).le)⟩

end CurveControl.Analysis

#print axioms CurveControl.Analysis.le_exp_of_deriv_right_le
#print axioms CurveControl.Analysis.coupled_exp_comparison_right
#print axioms CurveControl.Analysis.coupled_exp_comparison
#print axioms CurveControl.Analysis.family_coupled_exp_comparison_right
