import CurveControl.Analysis.EnergyIntegral

/-!
# Exponential comparison with derivatives only at interior times

The integrating-factor theorem already proved in `EnergyIntegral` supplies a
comparison that needs no initial-time derivative. This is the interface used
when geometric evolution is proved on the interior and continuity is available
up to the endpoints. The differential inequalities are explicit analysis inputs.
-/

open Set Real MeasureTheory

namespace CurveControl.Analysis

theorem le_exp_of_deriv_interior_le
    {f f' : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivWithinAt f (f' t) (Ioi t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t) :
    f b ≤ f a * exp (K * (b - a)) := by
  have he : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc a b) := by simp
  have h := weighted_energy_integral_le (E := fun _ => 0) hab hf hf' he
    (fun t ht => by simpa using hbound t ht)
  have hw : exp (-K * (b - a)) * f b ≤ f a := by
    simpa only [mul_zero, intervalIntegral.integral_zero, sub_nonneg] using h
  have hexp : exp (K * (b - a)) * exp (-K * (b - a)) = 1 := by
    rw [← exp_add]
    have hz : K * (b - a) + -K * (b - a) = 0 := by ring
    rw [hz, exp_zero]
  calc
    f b = exp (K * (b - a)) * (exp (-K * (b - a)) * f b) := by
      rw [← mul_assoc, hexp, one_mul]
    _ ≤ exp (K * (b - a)) * f a :=
      mul_le_mul_of_nonneg_left hw (exp_pos _).le
    _ = f a * exp (K * (b - a)) := mul_comm _ _

theorem coupled_exp_comparison_interior
    {L Q L' Q' : ℝ → ℝ} {a b c₁ c₂ : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn L (Icc a b)) (hQ : ContinuousOn Q (Icc a b))
    (hL' : ∀ t ∈ Ioo a b, HasDerivWithinAt L (L' t) (Ioi t) t)
    (hQ' : ∀ t ∈ Ioo a b, HasDerivWithinAt Q (Q' t) (Ioi t) t)
    (hLbound : ∀ t ∈ Ioo a b, L' t ≤ c₂ * L t)
    (hQbound : ∀ t ∈ Ioo a b, Q' t ≤ (c₁ + c₂) * Q t + c₁ * L t) :
    L b ≤ L a * exp (c₂ * (b - a)) ∧
      Q b + L b ≤ (Q a + L a) * exp ((c₁ + c₂) * (b - a)) := by
  constructor
  · exact le_exp_of_deriv_interior_le hab hL hL' hLbound
  · apply le_exp_of_deriv_interior_le hab (hQ.add hL)
      (fun t ht => (hQ' t ht).add (hL' t ht))
    intro t ht
    calc
      Q' t + L' t ≤ ((c₁ + c₂) * Q t + c₁ * L t) + c₂ * L t :=
        add_le_add (hQbound t ht) (hLbound t ht)
      _ = (c₁ + c₂) * (Q t + L t) := by ring

theorem coupled_exp_comparison_interior_on
    {L Q L' Q' : ℝ → ℝ} {a b c₁ c₂ : ℝ}
    (hL : ContinuousOn L (Icc a b)) (hQ : ContinuousOn Q (Icc a b))
    (hL' : ∀ t ∈ Ioo a b, HasDerivWithinAt L (L' t) (Ioi t) t)
    (hQ' : ∀ t ∈ Ioo a b, HasDerivWithinAt Q (Q' t) (Ioi t) t)
    (hLbound : ∀ t ∈ Ioo a b, L' t ≤ c₂ * L t)
    (hQbound : ∀ t ∈ Ioo a b, Q' t ≤ (c₁ + c₂) * Q t + c₁ * L t) :
    ∀ t ∈ Icc a b,
      L t ≤ L a * exp (c₂ * (t - a)) ∧
      Q t + L t ≤ (Q a + L a) * exp ((c₁ + c₂) * (t - a)) := by
  intro t ht
  have hi : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have ho : Ioo a t ⊆ Ioo a b := Ioo_subset_Ioo le_rfl ht.2
  exact coupled_exp_comparison_interior ht.1 (hL.mono hi) (hQ.mono hi)
    (fun r hr => hL' r (ho hr)) (fun r hr => hQ' r (ho hr))
    (fun r hr => hLbound r (ho hr)) (fun r hr => hQbound r (ho hr))

end CurveControl.Analysis
