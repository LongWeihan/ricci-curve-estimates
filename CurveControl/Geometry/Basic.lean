import MorganTianLib.Ch02.CovDerivAlongCurve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Actual metric quantities for a parametrized curve. All derivatives are the
upstream moving-foot chart derivatives, not independent scalar input data.
Totalized `deriv` and inverse give junk outside the differentiable immersed
case; `covDerivAlong_eq_of_hasCovDeriv` identifies the value under the genuine
upstream differentiability predicate. A closed curve has period one. Families
in subsequent files use `c t x`, with time first.
-/

open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff

noncomputable section

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- Period-one closure of the spatial parametrization. Smoothness is separate. -/
def IsClosedCurve (γ : ℝ → M) : Prop := Function.Periodic γ 1

/-- Speed for the actual Riemannian metric and intrinsic curve velocity. -/
def curveSpeed (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) : ℝ :=
  Real.sqrt (g.metricInner (γ x) (curveVelocity (I := I) γ x)
    (curveVelocity (I := I) γ x))

/-- Unit spatial tangent, meaningful when the spatial velocity is nonzero. -/
def unitTangent (g : RiemannianMetric I M) (γ : ℝ → M)
    (x : ℝ) : TangentSpace I (γ x) :=
  (curveSpeed g γ x)⁻¹ • curveVelocity (I := I) γ x

/-- Actual covariant derivative in the moving-foot chart. -/
def covDerivAlong (g : RiemannianMetric I M) (γ : ℝ → M)
    (W : ∀ x, TangentSpace I (γ x)) (x : ℝ) : TangentSpace I (γ x) :=
  deriv (chartFieldCoord (I := I) (γ x) γ W) x +
    chartChristoffelContraction (I := I) g (γ x)
      (deriv (chartLocalCurve (I := I) γ x) x) (W x)
      (extChartAt I (γ x) (γ x))

/-- Identifies the totalized derivative with a genuine covariant derivative. -/
theorem covDerivAlong_eq_of_hasCovDeriv (g : RiemannianMetric I M)
    (γ : ℝ → M) (W : ∀ x, TangentSpace I (γ x)) (x : ℝ) (D : E)
    (h : HasCovDerivAlongAt (I := I) g γ W x D) :
    covDerivAlong g γ W x = D := by
  obtain ⟨_, v, dV, hv, hV, hD⟩ := h
  unfold covDerivAlong
  rw [hv.deriv, hV.deriv]
  exact hD

/-- Curvature vector `∇ₛS = speed⁻¹ ∇ₓS`. -/
def curvatureVector (g : RiemannianMetric I M) (γ : ℝ → M)
    (x : ℝ) : TangentSpace I (γ x) :=
  (curveSpeed g γ x)⁻¹ • covDerivAlong g γ (unitTangent g γ) x

/-- Squared norm of the curvature vector. -/
def curvatureSq (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) : ℝ :=
  g.metricInner (γ x) (curvatureVector g γ x) (curvatureVector g γ x)

def curvature (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) : ℝ :=
  Real.sqrt (curvatureSq g γ x)

/-- Regularization that remains meaningful at zero curvature. -/
def regularizedCurvature (g : RiemannianMetric I M) (γ : ℝ → M)
    (ε x : ℝ) : ℝ := Real.sqrt (curvatureSq g γ x + ε ^ 2)

/-- Length over one parameter period; integrability follows later from smoothness. -/
def curveLength (g : RiemannianMetric I M) (γ : ℝ → M) : ℝ :=
  ∫ x in (0 : ℝ)..1, curveSpeed g γ x

/-- Total curvature with the actual arc-length density. -/
def totalCurvature (g : RiemannianMetric I M) (γ : ℝ → M) : ℝ :=
  ∫ x in (0 : ℝ)..1, curvature g γ x * curveSpeed g γ x

/-- Regularized total curvature with the actual arc-length density. -/
def regularizedTotalCurvature (g : RiemannianMetric I M) (γ : ℝ → M)
    (ε : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, regularizedCurvature g γ ε x * curveSpeed g γ x

/-- Integral of squared curvature against arc length. -/
def curvatureEnergy (g : RiemannianMetric I M) (γ : ℝ → M) : ℝ :=
  ∫ x in (0 : ℝ)..1, curvatureSq g γ x * curveSpeed g γ x

theorem curveSpeed_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) :
    0 ≤ curveSpeed g γ x := Real.sqrt_nonneg _

theorem curveSpeed_sq (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) :
    curveSpeed g γ x ^ 2 =
      g.metricInner (γ x) (curveVelocity (I := I) γ x) (curveVelocity (I := I) γ x) :=
  Real.sq_sqrt (g.metricInner_self_nonneg _ _)

theorem curveSpeed_pos (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ)
    (h : curveVelocity (I := I) γ x ≠ 0) : 0 < curveSpeed g γ x :=
  Real.sqrt_pos.2 (g.metricInner_self_pos _ _ h)

theorem unitTangent_unit (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ)
    (h : curveVelocity (I := I) γ x ≠ 0) :
    g.metricInner (γ x) (unitTangent g γ x) (unitTangent g γ x) = 1 := by
  have hv : curveSpeed g γ x ≠ 0 := ne_of_gt (curveSpeed_pos g γ x h)
  unfold unitTangent
  rw [g.metricInner_smul_left, g.metricInner_smul_right, ← curveSpeed_sq g γ x]
  field_simp

theorem curvatureSq_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) :
    0 ≤ curvatureSq g γ x := g.metricInner_self_nonneg _ _

theorem curvature_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) :
    0 ≤ curvature g γ x := Real.sqrt_nonneg _

theorem curvature_sq (g : RiemannianMetric I M) (γ : ℝ → M) (x : ℝ) :
    curvature g γ x ^ 2 = curvatureSq g γ x :=
  Real.sq_sqrt (curvatureSq_nonneg g γ x)

theorem regularizedCurvature_nonneg (g : RiemannianMetric I M) (γ : ℝ → M)
    (ε x : ℝ) : 0 ≤ regularizedCurvature g γ ε x := Real.sqrt_nonneg _

theorem regularizedCurvature_sq (g : RiemannianMetric I M) (γ : ℝ → M)
    (ε x : ℝ) : regularizedCurvature g γ ε x ^ 2 = curvatureSq g γ x + ε ^ 2 :=
  Real.sq_sqrt (add_nonneg (curvatureSq_nonneg g γ x) (sq_nonneg ε))

theorem regularizedCurvature_pos (g : RiemannianMetric I M) (γ : ℝ → M)
    (ε x : ℝ) (hε : 0 < ε) : 0 < regularizedCurvature g γ ε x := by
  apply Real.sqrt_pos.2
  exact add_pos_of_nonneg_of_pos (curvatureSq_nonneg g γ x) (sq_pos_of_pos hε)

end CurveControl.Geometry
