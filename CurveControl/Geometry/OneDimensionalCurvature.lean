import MorganTianLib.Ch01.RicciDivergence
import MorganTianLib.Ch03.RicciFlow.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Intrinsic flatness in dimension one. No curvature bound or flatness is assumed.
This applies to any positive constant scaling of any one-dimensional metric;
constructing the circle atlas and the product metric is separate. -/

open Riemannian MorganTianLib
open scoped Manifold ContDiff Bundle

noncomputable section
namespace CurveControl.Geometry

/-- **Math.** Alternation kills every algebraic curvature form in dimension one. -/
theorem algebraicCurvature_eq_zero_of_finrank_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {B : V → V → V → V → ℝ} (hB : Riemannian.IsAlgCurvatureForm B)
    (hdim : Module.finrank ℝ V = 1) (x y z w : V) : B x y z w = 0 := by
  by_cases hy : y = 0
  · subst y
    rw [hB.antisymm₁₂, hB.zero_left, neg_zero]
  · obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' y hy).mp hdim x
    rw [hB.smul_left, hB.self_left, mul_zero]

/-- **Math.** The Ricci trace of a one-dimensional algebraic curvature form vanishes. -/
theorem algebraicRicci_eq_zero_of_finrank_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {B : V → V → V → V → ℝ}
    (hB : Riemannian.IsAlgCurvatureForm B) (hdim : Module.finrank ℝ V = 1) (x y : V) :
    Riemannian.ricciForm hB x y = 0 := by
  rw [Riemannian.ricciForm_eq_sum hB x y (stdOrthonormalBasis ℝ V)]
  simp only [algebraicCurvature_eq_zero_of_finrank_one hB hdim, Finset.sum_const_zero]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Actual LC curvature, in the Morgan--Tian pointwise convention. -/
theorem curvatureFormAt_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (p : M) (x y z w : TangentSpace I p) :
    MorganTianLib.curvatureFormAt g nabla p x y z w = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact algebraicCurvature_eq_zero_of_finrank_one
    (MorganTianLib.isAlgCurvatureForm_curvatureFormAt g nabla hLC p) hdim x y z w

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Actual Ricci tensor for any Levi-Civita connection in dimension one. -/
theorem ricciAt_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (p : M) (x y : TangentSpace I p) : ricciAt g nabla hLC p x y = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact algebraicRicci_eq_zero_of_finrank_one
    (MorganTianLib.isAlgCurvatureForm_curvatureFormAt g nabla hLC p) hdim x y

/-- **Math.** The canonical Ricci tensor used by the Ricci-flow equation vanishes. -/
theorem ricciTensorAt_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (p : M) (x y : TangentSpace I p) : ricciTensorAt g p x y = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  unfold ricciTensorAt
  simp only [Riemannian.ricciBilin_apply]
  apply algebraicRicci_eq_zero_of_finrank_one
  exact hdim

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Ricci scalar field is identically zero, before differentiating it. -/
theorem ricciField_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y : SmoothVectorField I M) : ricciField g nabla hLC X Y = fun _ => 0 := by
  funext p
  exact ricciAt_eq_zero_of_finrank_one hdim g nabla hLC p (X p) (Y p)

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Covariant Ricci differentiation vanishes by differentiating the actual zero field. -/
theorem covRicci_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (U X Y : SmoothVectorField I M) (p : M) : covRicci g nabla hLC U X Y p = 0 := by
  unfold covRicci
  simp only [ricciField_eq_zero_of_finrank_one hdim g nabla hLC]
  simp [SmoothVectorField.dir]

/-- **Math.** Pointwise covariant Ricci tensor vanishes for arbitrary tangent inputs. -/
theorem covRicciAt_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (p : M) (u x y : TangentSpace I p) : covRicciAt g nabla hLC p u x y = 0 := by
  exact covRicci_eq_zero_of_finrank_one hdim g nabla hLC _ _ _ p

/-- **Math.** The canonical curvature tensor in the do Carmo convention vanishes. -/
theorem canonicalCurvatureFormAt_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (p : M) (x y z w : TangentSpace I p) :
    g.leviCivitaConnection.curvatureFormAt g p x y z w = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  exact algebraicCurvature_eq_zero_of_finrank_one
    (g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p) hdim x y z w

/-- **Math.** The full canonical curvature operator is zero, not merely its trace. -/
theorem canonicalCurvatureOperatorAt_eq_zero_of_finrank_one
    (hdim : Module.finrank ℝ E = 1) (g : Riemannian.RiemannianMetric I M)
    (p : M) (x y z : TangentSpace I p) :
    g.leviCivitaConnection.curvatureOperatorAt p x y z = 0 := by
  apply (g.metricInner_eq_iff_eq p _ _).mp
  intro w
  rw [g.metricInner_zero_left]
  exact canonicalCurvatureFormAt_eq_zero_of_finrank_one hdim g p x y z w

end CurveControl.Geometry
