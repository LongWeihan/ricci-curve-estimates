import CurveControl.Geometry.Flow

/-!
# Local coordinates of an actual curve flow

These lemmas pass from the manifold-valued input to a fixed local chart near
an interior spacetime point. The chart is local; no global chart or embedded
image is assumed. The time coordinate is first.
-/

open Set Filter Riemannian Riemannian.Geodesic MorganTianLib
open scoped Manifold Topology ContDiff

noncomputable section

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- Representation of the family in one fixed ambient chart. -/
def chartCurveFamily (α : M) (c : ℝ → ℝ → M) (p : ℝ × ℝ) : E :=
  extChartAt I α (c p.1 p.2)

namespace IsCurveShorteningFlowOn

variable {g : ℝ → Riemannian.RiemannianMetric I M} {c : ℝ → ℝ → M} {J : Set ℝ}
  (hc : IsCurveShorteningFlowOn (I := I) g c J)

include hc

theorem contMDiff_curve {t : ℝ} (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (c t) := by
  apply contMDiffOn_univ.mp
  exact hc.smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    (by intro x _; exact ⟨ht, mem_univ x⟩)

theorem contMDiffAt_family {p : ℝ × ℝ} (hp : p.1 ∈ interior J) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => c z.1 z.2) p := by
  exact hc.smooth.contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp hp) Filter.univ_mem)

theorem contDiffAt_chartCurveFamily (α : M) {p : ℝ × ℝ}
    (hp : p.1 ∈ interior J) (hα : c p.1 p.2 ∈ (chartAt H α).source) :
    ContDiffAt ℝ ∞ (chartCurveFamily (I := I) α c) p := by
  have h := (contMDiffAt_extChartAt' (I := I) hα).comp p (hc.contMDiffAt_family hp)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffAt

theorem chartVelocity_eq_spatialFDeriv (α : M) {t x : ℝ}
    (ht : t ∈ interior J) (hα : c t x ∈ (chartAt H α).source) :
    chartFieldCoord (I := I) α (c t) (curveVelocity (I := I) (c t)) x =
      fderiv ℝ (chartCurveFamily (I := I) α c) (t, x) (0, 1) := by
  have hc' := hc.contMDiff_curve (interior_subset ht)
  have hmem : ∀ᶠ y in 𝓝 x, c t y ∈ (chartAt H α).source :=
    hc'.continuous.continuousAt ((chartAt H α).open_source.mem_nhds hα)
  have hd := (hc.contDiffAt_chartCurveFamily α (p := (t, x)) ht hα).differentiableAt (by simp)
  have hs : HasDerivAt (fun y : ℝ => (t, y)) (0, 1) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  exact chartFieldCoord_curveVelocity_eq hmem (hd.hasFDerivAt.comp_hasDerivAt x hs)

theorem chartCurvature_eq_timeFDeriv (α : M) {t x : ℝ}
    (ht : t ∈ interior J) (hα : c t x ∈ (chartAt H α).source) :
    tangentCoordChange I (c t x) α (c t x) (curvatureVector (g t) (c t) x) =
      fderiv ℝ (chartCurveFamily (I := I) α c) (t, x) (1, 0) := by
  have hpath : ContinuousAt (fun s : ℝ => c s x) t :=
    (hc.contMDiffAt_family ht).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)
  have hmem : ∀ᶠ s in 𝓝 t, c s x ∈ (chartAt H α).source :=
    hpath ((chartAt H α).open_source.mem_nhds hα)
  have hd := (hc.contDiffAt_chartCurveFamily α (p := (t, x)) ht hα).differentiableAt (by simp)
  have hs : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hdtime : HasDerivAt (fun s => extChartAt I α (c s x))
      (fderiv ℝ (chartCurveFamily (I := I) α c) (t, x) (1, 0)) t :=
    by simpa only [Function.comp_def, chartCurveFamily] using
      (hd.hasFDerivAt.comp_hasDerivAt t hs)
  have hcoord := chartFieldCoord_curveVelocity_eq (I := I)
    (x := α) (γ := fun s => c s x) hmem hdtime
  change tangentCoordChange I (c t x) α (c t x)
    (curveVelocity (I := I) (fun s => c s x) t) = _ at hcoord
  rw [hc.timeVelocity_eq_curvatureVector ht x] at hcoord
  exact hcoord

end IsCurveShorteningFlowOn

end CurveControl.Geometry
