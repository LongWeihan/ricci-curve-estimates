import CurveControl.Geometry.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Deriv

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

/-- A smooth curve has a smooth representative in its moving-foot chart. -/
theorem contDiffAt_chartLocalCurve (γ : ℝ → M) (x : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ x) :
    ContDiffAt ℝ ∞ (chartLocalCurve (I := I) γ x) x := by
  exact (contMDiffAt_extChartAt.comp x hγ).contDiffAt

/-- Continuity keeps the curve in the anchor chart near its base parameter. -/
theorem eventually_mem_chartSource (γ : ℝ → M) (x : ℝ)
    (hγ : ContinuousAt γ x) :
    ∀ᶠ y in 𝓝 x, γ y ∈ (chartAt H (γ x)).source :=
  hγ ((chartAt H (γ x)).open_source.mem_nhds (mem_chart_source H (γ x)))

/-- Differentiability of the actual chart representatives suffices to eliminate
the totalized-derivative junk in `covDerivAlong`. -/
theorem hasCovDerivAlongAt_covDerivAlong (g : RiemannianMetric I M)
    (γ : ℝ → M) (W : ∀ x, TangentSpace I (γ x)) (x : ℝ)
    (hmem : ∀ᶠ y in 𝓝 x, γ y ∈ (chartAt H (γ x)).source)
    (hγ : DifferentiableAt ℝ (chartLocalCurve (I := I) γ x) x)
    (hW : DifferentiableAt ℝ (chartFieldCoord (I := I) (γ x) γ W) x) :
    HasCovDerivAlongAt (I := I) g γ W x (covDerivAlong g γ W x) := by
  exact ⟨hmem, _, _, hγ.hasDerivAt, hW.hasDerivAt, rfl⟩

/-- The velocity field has smooth coordinates near every parameter. This uses
the chart-transition theorem, rather than differentiating moving charts. -/
theorem contDiffAt_chartFieldCoord_velocity (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (x : ℝ) :
    ContDiffAt ℝ ∞
      (chartFieldCoord (I := I) (γ x) γ (curveVelocity (I := I) γ)) x := by
  have hc := contDiffAt_chartLocalCurve γ x (hγ.contMDiffAt)
  have hd : ContDiffAt ℝ ∞ (deriv (chartLocalCurve (I := I) γ x)) x :=
    hc.derivWithin (by simp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_mem_chartSource (H := H) γ x (hγ.continuous.continuousAt)] with y hy
  have hmem : ∀ᶠ z in 𝓝 y, γ z ∈ (chartAt H (γ x)).source :=
    hγ.continuous.continuousAt ((chartAt H (γ x)).open_source.mem_nhds hy)
  have hchart : ContDiffAt ℝ ∞ (chartLocalCurve (I := I) γ x) y :=
    ((contMDiffAt_extChartAt' hy).comp y hγ.contMDiffAt).contDiffAt
  exact chartFieldCoord_curveVelocity_eq hmem
    (hchart.differentiableAt (by simp)).hasDerivAt

/-- Smoothness of the curve supplies the actual covariant acceleration. -/
theorem hasCovDerivAlongAt_velocity (g : RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (x : ℝ) :
    HasCovDerivAlongAt (I := I) g γ (curveVelocity (I := I) γ) x
      (covDerivAlong g γ (curveVelocity (I := I) γ) x) := by
  apply hasCovDerivAlongAt_covDerivAlong
  · exact eventually_mem_chartSource (H := H) γ x hγ.continuous.continuousAt
  · exact (contDiffAt_chartLocalCurve γ x hγ.contMDiffAt).differentiableAt (by simp)
  · exact (contDiffAt_chartFieldCoord_velocity γ hγ x).differentiableAt (by simp)

/-- Spatial speed derivative in a fixed ambient metric, derived from metric
compatibility. The covariant derivative hypothesis is the upstream genuine
chart differentiability predicate, not a speed evolution assumption. -/
theorem hasDerivAt_curveSpeed (g : RiemannianMetric I M) (γ : ℝ → M)
    (x : ℝ) (D : E) (himm : curveVelocity (I := I) γ x ≠ 0)
    (hD : HasCovDerivAlongAt (I := I) g γ (curveVelocity (I := I) γ) x D) :
    HasDerivAt (curveSpeed g γ)
      ((g.metricInner (γ x) D (curveVelocity (I := I) γ x) +
        g.metricInner (γ x) (curveVelocity (I := I) γ x) D) /
        (2 * curveSpeed g γ x)) x := by
  exact (hD.hasDerivAt_metricInner hD).sqrt
    (ne_of_gt (g.metricInner_self_pos _ _ himm))

/-- Curvature is orthogonal to the unit tangent. Unit length is proved from
immersion, and metric compatibility differentiates that identity. -/
theorem curvatureVector_orthogonal (g : RiemannianMetric I M) (γ : ℝ → M)
    (x : ℝ) (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0)
    (hS : HasCovDerivAlongAt (I := I) g γ (unitTangent g γ) x
      (covDerivAlong g γ (unitTangent g γ) x)) :
    g.metricInner (γ x) (curvatureVector g γ x) (unitTangent g γ x) = 0 := by
  have hconst : (fun y => g.metricInner (γ y) (unitTangent g γ y)
      (unitTangent g γ y)) = fun _ => (1 : ℝ) := by
    funext y
    exact unitTangent_unit g γ y (himm y)
  have hprod := hS.hasDerivAt_metricInner hS
  rw [hconst] at hprod
  have hzero := hprod.unique (hasDerivAt_const x (1 : ℝ))
  rw [g.metricInner_comm (γ x) (unitTangent g γ x)
    (covDerivAlong g γ (unitTangent g γ) x)] at hzero
  have hperp : g.metricInner (γ x) (covDerivAlong g γ (unitTangent g γ) x)
      (unitTangent g γ x) = 0 := by linarith
  unfold curvatureVector
  rw [g.metricInner_smul_left, hperp, mul_zero]

/-- Unit tangent covariant differentiability follows from smooth immersion. -/
theorem hasCovDerivAlongAt_unitTangent (g : RiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (x : ℝ)
    (himm : curveVelocity (I := I) γ x ≠ 0) :
    HasCovDerivAlongAt (I := I) g γ (unitTangent g γ) x
      (covDerivAlong g γ (unitTangent g γ) x) := by
  have hX := hasCovDerivAlongAt_velocity g γ hγ x
  have hv := hasDerivAt_curveSpeed g γ x _ himm hX
  have hinv := hv.inv (ne_of_gt (curveSpeed_pos g γ x himm))
  have hS := HasCovDerivAlongAt.smul_fun hinv hX
  change HasCovDerivAlongAt (I := I) g γ (unitTangent g γ) x _ at hS
  rw [covDerivAlong_eq_of_hasCovDeriv g γ (unitTangent g γ) x _ hS]
  exact hS

/-- Orthogonality for a smooth immersed curve, with no derivative or
orthogonality hypothesis on its curvature vector. -/
theorem curvatureVector_orthogonal_of_contMDiff (g : RiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (himm : ∀ y, curveVelocity (I := I) γ y ≠ 0) (x : ℝ) :
    g.metricInner (γ x) (curvatureVector g γ x) (unitTangent g γ x) = 0 :=
  curvatureVector_orthogonal g γ x himm
    (hasCovDerivAlongAt_unitTangent g γ hγ x (himm x))


end CurveControl.Geometry
