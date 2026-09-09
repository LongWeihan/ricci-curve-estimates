import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fixed-parameter weighted curve integrals

These are analysis lemmas only. A geometric caller must supply the actual time
derivatives, the domination hypotheses, and the periodic spatial derivatives.
The measure is Lebesgue measure on the fixed parameter interval `(0,1]`.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

namespace CurveControl.Analysis

/-- Differentiation of a moving weight on a fixed parameter interval. The
derivative bound is uniform on one time neighborhood and integrable in space. -/
theorem hasDerivAt_weightedIntegral
    {f v ft vt : ℝ → ℝ → ℝ} {t : ℝ} {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 t)
    (hmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (fun x => f u x * v u x)
      (volume.restrict (Ioc 0 1)))
    (hint : Integrable (fun x => f t x * v t x) (volume.restrict (Ioc 0 1)))
    (hdmeas : AEStronglyMeasurable (fun x => ft t x * v t x + f t x * vt t x)
      (volume.restrict (Ioc 0 1)))
    (hbound : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ s,
      ‖ft u x * v u x + f u x * vt u x‖ ≤ bound x)
    (hbi : Integrable bound (volume.restrict (Ioc 0 1)))
    (hf : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ s,
      HasDerivAt (fun z => f z x) (ft u x) u)
    (hv : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ s,
      HasDerivAt (fun z => v z x) (vt u x) u) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, f u x * v u x)
      (∫ x in (0 : ℝ)..1, ft t x * v t x + f t x * vt t x) t := by
  have hd : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ s,
      HasDerivAt (fun z => f z x * v z x)
        (ft u x * v u x + f u x * vt u x) u := by
    filter_upwards [hf, hv] with x hfx hvx
    intro u hu
    exact (hfx u hu).mul (hvx u hu)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    hmeas hint hdmeas hbound hbi hd).2
  simpa only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using h

/-- Substitution of a proved density evolution law into the weighted first
variation. This theorem does not assert or assume any unproved geometric law. -/
theorem hasDerivAt_weightedIntegral_of_densityEvolution
    {f v ft vt q r : ℝ → ℝ → ℝ} {t : ℝ}
    (hfirst : HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, f u x * v u x)
      (∫ x in (0 : ℝ)..1, ft t x * v t x + f t x * vt t x) t)
    (hevol : ∀ x ∈ Icc (0 : ℝ) 1, vt t x = -(q t x + r t x) * v t x) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, f u x * v u x)
      (∫ x in (0 : ℝ)..1, (ft t x - f t x * (q t x + r t x)) * v t x) t := by
  convert hfirst using 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hx
  dsimp only
  rw [hevol x hx]
  simp only [sub_eq_add_neg, add_mul, mul_neg, neg_mul, mul_assoc]

/-- Continuity of weighted integrals on a closed time interval follows from
dominated convergence, requiring no time derivative at either endpoint. -/
theorem continuousOn_weightedIntegral
    {f v : ℝ → ℝ → ℝ} {a b : ℝ} {bound : ℝ → ℝ}
    (hmeas : ∀ t ∈ Icc a b, AEStronglyMeasurable (fun x => f t x * v t x)
      (volume.restrict (Ioc 0 1)))
    (hbound : ∀ t ∈ Icc a b, ∀ᵐ x ∂volume.restrict (Ioc 0 1),
      ‖f t x * v t x‖ ≤ bound x)
    (hbi : Integrable bound (volume.restrict (Ioc 0 1)))
    (hcont : ∀ᵐ x ∂volume.restrict (Ioc 0 1),
      ContinuousOn (fun t => f t x * v t x) (Icc a b)) :
    ContinuousOn (fun t => ∫ x in (0 : ℝ)..1, f t x * v t x) (Icc a b) := by
  have h := continuousOn_of_dominated hmeas hbound hbi hcont
  simpa only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using h

/-- Interior-time first variation. Only times strictly between `a` and `b`
need derivatives; no smooth extension through the initial endpoint is needed.
Together with `continuousOn_weightedIntegral` this supplies the analytic
regularity used by closed-interval comparison arguments. -/
theorem hasDerivAt_weightedIntegral_interior
    {f v ft vt : ℝ → ℝ → ℝ} {a b t : ℝ} {bound : ℝ → ℝ}
    (ht : t ∈ Ioo a b)
    (hmeas : ∀ u ∈ Ioo a b, AEStronglyMeasurable (fun x => f u x * v u x)
      (volume.restrict (Ioc 0 1)))
    (hint : Integrable (fun x => f t x * v t x) (volume.restrict (Ioc 0 1)))
    (hdmeas : AEStronglyMeasurable (fun x => ft t x * v t x + f t x * vt t x)
      (volume.restrict (Ioc 0 1)))
    (hbound : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ Ioo a b,
      ‖ft u x * v u x + f u x * vt u x‖ ≤ bound x)
    (hbi : Integrable bound (volume.restrict (Ioc 0 1)))
    (hf : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ Ioo a b,
      HasDerivAt (fun z => f z x) (ft u x) u)
    (hv : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ Ioo a b,
      HasDerivAt (fun z => v z x) (vt u x) u) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, f u x * v u x)
      (∫ x in (0 : ℝ)..1, ft t x * v t x + f t x * vt t x) t := by
  apply hasDerivAt_weightedIntegral (Ioo_mem_nhds ht.1 ht.2)
    _ hint hdmeas hbound hbi hf hv
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
  exact hmeas u hu

/-- Arclength differentiation in a fixed regular curve parameter. -/
noncomputable def arcDeriv (v f : ℝ → ℝ) (x : ℝ) : ℝ := deriv f x / v x

/-- A periodic flux derivative has zero integral, by the fundamental theorem
of calculus. The zero integral is a conclusion, never a hypothesis. -/
theorem integral_deriv_eq_zero_of_endpoints
    {g : ℝ → ℝ}
    (hdiff : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ g x)
    (hint : IntervalIntegrable (deriv g) volume 0 1)
    (hperiod : g 1 = g 0) :
    (∫ x in (0 : ℝ)..1, deriv g x) = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub
    (by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hdiff) hint,
    hperiod, sub_self]

/-- Weighted spatial second derivatives integrate to zero when the actual
first arclength derivative has matching endpoint values. The regularity and
endpoint conditions must be verified by the periodic geometric caller. -/
theorem integral_arcDeriv_arcDeriv_eq_zero
    {f v : ℝ → ℝ}
    (hv : ∀ x ∈ Icc (0 : ℝ) 1, 0 < v x)
    (hdiff : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (arcDeriv v f) x)
    (hint : IntervalIntegrable (deriv (arcDeriv v f)) volume 0 1)
    (hperiod : arcDeriv v f 1 = arcDeriv v f 0) :
    (∫ x in (0 : ℝ)..1, arcDeriv v (arcDeriv v f) x * v x) = 0 := by
  calc
    _ = ∫ x in (0 : ℝ)..1, deriv (arcDeriv v f) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hx
      exact div_mul_cancel₀ _ (ne_of_gt (hv x hx))
    _ = 0 := integral_deriv_eq_zero_of_endpoints hdiff hint hperiod

end CurveControl.Analysis

#print axioms CurveControl.Analysis.hasDerivAt_weightedIntegral
#print axioms CurveControl.Analysis.hasDerivAt_weightedIntegral_of_densityEvolution
#print axioms CurveControl.Analysis.continuousOn_weightedIntegral
#print axioms CurveControl.Analysis.hasDerivAt_weightedIntegral_interior
#print axioms CurveControl.Analysis.integral_deriv_eq_zero_of_endpoints
#print axioms CurveControl.Analysis.integral_arcDeriv_arcDeriv_eq_zero
