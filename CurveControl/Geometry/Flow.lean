import CurveControl.Geometry.Basic
import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Smooth curve-shortening flow: geometric input

The curve family is `c t x`, with period one in `x`. Only smooth existence,
immersion, closure and the defining curve-shortening equation are inputs.
No speed, curvature or integral evolution estimate is part of this predicate.

Time derivatives in the input are within the time set. This avoids imposing
an artificial extension of the PDE before an initial time or beyond a final
time. At interior times the equation gives the ordinary chart derivative.
-/

open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff

noncomputable section

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- A genuine smooth immersed closed curve-shortening flow in a metric family.
The Ricci-flow equation for the metric is a separate upstream predicate. -/
structure IsCurveShorteningFlowOn (g : ℝ → Riemannian.RiemannianMetric I M)
    (c : ℝ → ℝ → M) (J : Set ℝ) : Prop where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
    (fun p : ℝ × ℝ => c p.1 p.2) (J ×ˢ (Set.univ : Set ℝ))
  closed : ∀ t ∈ J, IsClosedCurve (c t)
  immersed : ∀ t ∈ J, ∀ x, curveVelocity (I := I) (c t) x ≠ 0
  equation : ∀ t ∈ J, ∀ x,
    HasDerivWithinAt (chartLocalCurve (I := I) (fun s => c s x) t)
      (curvatureVector (g t) (c t) x) J t

namespace IsCurveShorteningFlowOn

variable {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
  (hc : IsCurveShorteningFlowOn (I := I) g c J)

include hc

theorem speed_pos {t : ℝ} (ht : t ∈ J) (x : ℝ) :
    0 < curveSpeed (g t) (c t) x :=
  curveSpeed_pos (g t) (c t) x (hc.immersed t ht x)

theorem tangent_unit {t : ℝ} (ht : t ∈ J) (x : ℝ) :
    (g t).metricInner (c t x) (unitTangent (g t) (c t) x)
      (unitTangent (g t) (c t) x) = 1 :=
  unitTangent_unit (g t) (c t) x (hc.immersed t ht x)

theorem hasDerivAt_timeChart {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasDerivAt (chartLocalCurve (I := I) (fun s => c s x) t)
      (curvatureVector (g t) (c t) x) t :=
  (hc.equation t (interior_subset ht) x).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)

theorem timeVelocity_eq_curvatureVector {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    curveVelocity (I := I) (fun s => c s x) t = curvatureVector (g t) (c t) x := by
  exact (hc.hasDerivAt_timeChart ht x).deriv

end IsCurveShorteningFlowOn

end CurveControl.Geometry
