import CurveControl.Analysis.WeightedIntegral
import CurveControl.Analysis.RegularizedNorm

/-!
# Integrating local curve inequalities

This analysis layer integrates a supplied density evolution and regularized
scalar PDE. Geometric applications must separately prove those local equations
and the regularity/periodicity hypotheses. No theorem here asserts a Ricci-flow
or curve-shortening evolution equation.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

namespace CurveControl.Analysis

/-- Explicit analytic hypotheses for the fixed-parameter differentiation
theorem. This packages local derivative and domination data, not a conclusion
about the derivative of the whole integral. -/
structure MovingWeightData (f v ft vt : ℝ → ℝ → ℝ) (t : ℝ) where
  timeSet : Set ℝ
  bound : ℝ → ℝ
  neighborhood : timeSet ∈ 𝓝 t
  measurable : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (fun x => f u x * v u x)
    (volume.restrict (Ioc 0 1))
  integrable : Integrable (fun x => f t x * v t x) (volume.restrict (Ioc 0 1))
  derivative_measurable : AEStronglyMeasurable
    (fun x => ft t x * v t x + f t x * vt t x) (volume.restrict (Ioc 0 1))
  derivative_bound : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ timeSet,
    ‖ft u x * v u x + f u x * vt u x‖ ≤ bound x
  bound_integrable : Integrable bound (volume.restrict (Ioc 0 1))
  function_derivative : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ timeSet,
    HasDerivAt (fun z => f z x) (ft u x) u
  weight_derivative : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ∀ u ∈ timeSet,
    HasDerivAt (fun z => v z x) (vt u x) u

theorem MovingWeightData.hasDerivAt {f v ft vt : ℝ → ℝ → ℝ} {t : ℝ}
    (D : MovingWeightData f v ft vt t) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, f u x * v u x)
      (∫ x in (0 : ℝ)..1, ft t x * v t x + f t x * vt t x) t :=
  hasDerivAt_weightedIntegral D.neighborhood D.measurable D.integrable
    D.derivative_measurable D.derivative_bound D.bound_integrable
    D.function_derivative D.weight_derivative

/-- The favorable cubic reaction is absorbed by the negative density term. -/
theorem sqrt_cube_sub_regularized_mul_nonpos {q ε : ℝ} (hq : 0 ≤ q) :
    Real.sqrt q ^ 3 - regularizedNorm q ε * q ≤ 0 := by
  have hm := mul_le_mul_of_nonneg_right (sqrt_le_regularizedNorm q ε) hq
  have hs := Real.sq_sqrt hq
  calc
    _ = Real.sqrt q * q - regularizedNorm q ε * q := by rw [pow_succ, hs]; ring
    _ ≤ 0 := sub_nonpos.mpr hm

theorem regularized_density_pointwise_le {q ε htime diffusion r B C : ℝ}
    (hq : 0 ≤ q) (hr : |r| ≤ B)
    (hpde : htime ≤ diffusion + Real.sqrt q ^ 3 + C * (regularizedNorm q ε + 1)) :
    htime - regularizedNorm q ε * (q + r) ≤
      diffusion + (C + B) * regularizedNorm q ε + C := by
  have hc := sqrt_cube_sub_regularized_mul_nonpos (ε := ε) hq
  have hn := regularizedNorm_nonneg q ε
  have hb := mul_le_mul_of_nonneg_left (abs_le.mp hr).1 hn
  nlinarith

/-- The length variation retains its full negative squared-curvature energy. -/
theorem integral_density_le {q r v : ℝ → ℝ} {B : ℝ}
    (hv : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ v x)
    (hr : ∀ x ∈ Icc (0 : ℝ) 1, |r x| ≤ B)
    (ileft : IntervalIntegrable (fun x => -(q x + r x) * v x) volume 0 1)
    (iv : IntervalIntegrable v volume 0 1)
    (iqv : IntervalIntegrable (fun x => q x * v x) volume 0 1) :
    (∫ x in (0 : ℝ)..1, -(q x + r x) * v x) ≤
      B * (∫ x in (0 : ℝ)..1, v x) - ∫ x in (0 : ℝ)..1, q x * v x := by
  have hm : (∫ x in (0 : ℝ)..1, -(q x + r x) * v x) ≤
      ∫ x in (0 : ℝ)..1, B * v x - q x * v x := by
    apply intervalIntegral.integral_mono_on zero_le_one ileft ((iv.const_mul B).sub iqv)
    intro x hx
    have hb := mul_le_mul_of_nonneg_right (abs_le.mp (hr x hx)).1 (hv x hx)
    nlinarith
  simpa only [intervalIntegral.integral_sub (iv.const_mul B) iqv,
    intervalIntegral.integral_const_mul] using hm

/-- An integrated regularized PDE, with an explicit diffusion integral.
The following periodic version proves that integral vanishes by FTC. -/
theorem integral_regularized_density_le {q r v htime diffusion : ℝ → ℝ} {ε B C : ℝ}
    (hq : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x)
    (hv : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ v x)
    (hr : ∀ x ∈ Icc (0 : ℝ) 1, |r x| ≤ B)
    (hpde : ∀ x ∈ Icc (0 : ℝ) 1,
      htime x ≤ diffusion x + Real.sqrt (q x) ^ 3 + C * (regularizedNorm (q x) ε + 1))
    (ileft : IntervalIntegrable
      (fun x => (htime x - regularizedNorm (q x) ε * (q x + r x)) * v x) volume 0 1)
    (idiff : IntervalIntegrable (fun x => diffusion x * v x) volume 0 1)
    (ihv : IntervalIntegrable (fun x => regularizedNorm (q x) ε * v x) volume 0 1)
    (iv : IntervalIntegrable v volume 0 1) :
    (∫ x in (0 : ℝ)..1, (htime x - regularizedNorm (q x) ε * (q x + r x)) * v x) ≤
      (∫ x in (0 : ℝ)..1, diffusion x * v x) +
      (C + B) * (∫ x in (0 : ℝ)..1, regularizedNorm (q x) ε * v x) +
      C * (∫ x in (0 : ℝ)..1, v x) := by
  have hm : (∫ x in (0 : ℝ)..1,
      (htime x - regularizedNorm (q x) ε * (q x + r x)) * v x) ≤
      ∫ x in (0 : ℝ)..1,
        (diffusion x * v x + (C + B) * (regularizedNorm (q x) ε * v x)) + C * v x := by
    apply intervalIntegral.integral_mono_on zero_le_one ileft
      ((idiff.add (ihv.const_mul (C + B))).add (iv.const_mul C))
    intro x hx
    have h := mul_le_mul_of_nonneg_right
      (regularized_density_pointwise_le (hq x hx) (hr x hx) (hpde x hx)) (hv x hx)
    calc
      _ ≤ (diffusion x + (C + B) * regularizedNorm (q x) ε + C) * v x := h
      _ = _ := by ring
  simpa only [intervalIntegral.integral_add (idiff.add (ihv.const_mul (C + B)))
      (iv.const_mul C), intervalIntegral.integral_add idiff (ihv.const_mul (C + B)),
      intervalIntegral.integral_const_mul] using hm

theorem hasDerivAt_length {q r v vt : ℝ → ℝ → ℝ} {t : ℝ}
    (D : MovingWeightData (fun _ _ => 1) v (fun _ _ => 0) vt t)
    (hevol : ∀ x ∈ Icc (0 : ℝ) 1, vt t x = -(q t x + r t x) * v t x) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..1, v u x)
      (∫ x in (0 : ℝ)..1, -(q t x + r t x) * v t x) t := by
  have hd := hasDerivAt_weightedIntegral_of_densityEvolution
    (f := fun _ _ => 1) (ft := fun _ _ => 0) D.hasDerivAt hevol
  simpa only [one_mul, zero_sub] using hd

theorem deriv_length_le {q r v vt : ℝ → ℝ → ℝ} {t B : ℝ}
    (D : MovingWeightData (fun _ _ => 1) v (fun _ _ => 0) vt t)
    (hevol : ∀ x ∈ Icc (0 : ℝ) 1, vt t x = -(q t x + r t x) * v t x)
    (hv : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ v t x)
    (hr : ∀ x ∈ Icc (0 : ℝ) 1, |r t x| ≤ B)
    (ileft : IntervalIntegrable (fun x => -(q t x + r t x) * v t x) volume 0 1)
    (iv : IntervalIntegrable (v t) volume 0 1)
    (iqv : IntervalIntegrable (fun x => q t x * v t x) volume 0 1) :
    deriv (fun u => ∫ x in (0 : ℝ)..1, v u x) t ≤
      B * (∫ x in (0 : ℝ)..1, v t x) - ∫ x in (0 : ℝ)..1, q t x * v t x := by
  rw [(hasDerivAt_length D hevol).deriv]
  exact integral_density_le hv hr ileft iv iqv

/-- A genuine derivative inequality for the regularized weighted integral.
Its derivative is obtained from local time derivatives, and its diffusion
term is removed using the actual periodic first arclength derivative. -/
theorem deriv_regularizedTotal_le {q r v ht vt : ℝ → ℝ → ℝ} {t ε B C : ℝ}
    (D : MovingWeightData (fun u x => regularizedNorm (q u x) ε) v ht vt t)
    (hevol : ∀ x ∈ Icc (0 : ℝ) 1, vt t x = -(q t x + r t x) * v t x)
    (hq : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q t x)
    (hv : ∀ x ∈ Icc (0 : ℝ) 1, 0 < v t x)
    (hr : ∀ x ∈ Icc (0 : ℝ) 1, |r t x| ≤ B)
    (hpde : ∀ x ∈ Icc (0 : ℝ) 1, ht t x ≤
      arcDeriv (v t) (arcDeriv (v t) (fun y => regularizedNorm (q t y) ε)) x +
      Real.sqrt (q t x) ^ 3 + C * (regularizedNorm (q t x) ε + 1))
    (ileft : IntervalIntegrable
      (fun x => (ht t x - regularizedNorm (q t x) ε * (q t x + r t x)) * v t x) volume 0 1)
    (idiff : IntervalIntegrable
      (fun x => arcDeriv (v t) (arcDeriv (v t) (fun y => regularizedNorm (q t y) ε)) x * v t x)
      volume 0 1)
    (ihv : IntervalIntegrable (fun x => regularizedNorm (q t x) ε * v t x) volume 0 1)
    (iv : IntervalIntegrable (v t) volume 0 1)
    (hspatial : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (arcDeriv (v t) (fun y => regularizedNorm (q t y) ε)) x)
    (iflux : IntervalIntegrable
      (deriv (arcDeriv (v t) (fun y => regularizedNorm (q t y) ε))) volume 0 1)
    (hperiod : arcDeriv (v t) (fun y => regularizedNorm (q t y) ε) 1 =
      arcDeriv (v t) (fun y => regularizedNorm (q t y) ε) 0) :
    deriv (fun u => ∫ x in (0 : ℝ)..1, regularizedNorm (q u x) ε * v u x) t ≤
      (C + B) * (∫ x in (0 : ℝ)..1, regularizedNorm (q t x) ε * v t x) +
      C * (∫ x in (0 : ℝ)..1, v t x) := by
  rw [(hasDerivAt_weightedIntegral_of_densityEvolution D.hasDerivAt hevol).deriv]
  have h := integral_regularized_density_le hq (fun x hx => (hv x hx).le) hr hpde
    ileft idiff ihv iv
  rw [integral_arcDeriv_arcDeriv_eq_zero hv hspatial iflux hperiod, zero_add] at h
  exact h

end CurveControl.Analysis

#print axioms CurveControl.Analysis.MovingWeightData.hasDerivAt
#print axioms CurveControl.Analysis.sqrt_cube_sub_regularized_mul_nonpos
#print axioms CurveControl.Analysis.regularized_density_pointwise_le
#print axioms CurveControl.Analysis.integral_density_le
#print axioms CurveControl.Analysis.integral_regularized_density_le
#print axioms CurveControl.Analysis.hasDerivAt_length
#print axioms CurveControl.Analysis.deriv_length_le
#print axioms CurveControl.Analysis.deriv_regularizedTotal_le
