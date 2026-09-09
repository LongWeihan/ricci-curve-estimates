import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Ricci
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Ricci traces under an orthogonal product decomposition

This algebraic step uses the actual Ricci trace of a curvature form. A geometric
application must prove the curvature splitting and provide the genuine metric
isometry of tangent spaces; neither conclusion is asserted here.
-/

noncomputable section

namespace CurveControl.Geometry

open Riemannian

variable {V E F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The Ricci trace is invariant under a genuine linear isometry. -/
theorem ricciForm_isometry
    {B : V → V → V → V → ℝ} {C : E → E → E → E → ℝ}
    (hB : IsAlgCurvatureForm B) (hC : IsAlgCurvatureForm C)
    (e : V ≃ₗᵢ[ℝ] E)
    (h : ∀ x y z w, C (e x) (e y) (e z) (e w) = B x y z w)
    (x y : V) : ricciForm hC (e x) (e y) = ricciForm hB x y := by
  classical
  let b := stdOrthonormalBasis ℝ V
  rw [ricciForm_eq_sum hC _ _ (b.map e), ricciForm_eq_sum hB _ _ b]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [OrthonormalBasis.map_apply] using h x (b i) y (b i)

/-- Tracing a curvature form that splits over an orthogonal product gives the
sum of the two factor Ricci forms. The isometry prevents a model norm from being
silently substituted for the Riemannian metric. -/
theorem ricciForm_product
    {B : V → V → V → V → ℝ}
    {B₁ : E → E → E → E → ℝ} {B₂ : F → F → F → F → ℝ}
    (hB : IsAlgCurvatureForm B) (h₁ : IsAlgCurvatureForm B₁)
    (h₂ : IsAlgCurvatureForm B₂)
    (e : V ≃ₗᵢ[ℝ] WithLp 2 (E × F))
    (h : ∀ x y z w,
      B x y z w =
        B₁ (e x).ofLp.1 (e y).ofLp.1 (e z).ofLp.1 (e w).ofLp.1 +
        B₂ (e x).ofLp.2 (e y).ofLp.2 (e z).ofLp.2 (e w).ofLp.2)
    (x y : V) :
    ricciForm hB x y =
      ricciForm h₁ (e x).ofLp.1 (e y).ofLp.1 +
      ricciForm h₂ (e x).ofLp.2 (e y).ofLp.2 := by
  classical
  let b₁ := stdOrthonormalBasis ℝ E
  let b₂ := stdOrthonormalBasis ℝ F
  rw [ricciForm_eq_sum hB _ _ ((b₁.prod b₂).map e.symm),
    ricciForm_eq_sum h₁ _ _ b₁, ricciForm_eq_sum h₂ _ _ b₂,
    Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · simp only [OrthonormalBasis.map_apply, h, LinearIsometryEquiv.apply_symm_apply,
      OrthonormalBasis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, WithLp.ofLp_toLp, h₂.zero_two, add_zero]
  · simp only [OrthonormalBasis.map_apply, h, LinearIsometryEquiv.apply_symm_apply,
      OrthonormalBasis.prod_apply, Sum.elim_inr, Function.comp_apply,
      LinearMap.inr_apply, WithLp.ofLp_toLp, h₁.zero_two, zero_add]

end CurveControl.Geometry
