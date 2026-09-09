import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! A genuine Hilbert model for a product manifold, retaining the original atlas.
The product metric is pulled back along the identity diffeomorphism between
models. No inner-product instance is imposed on the max-norm product. -/

open Riemannian
open scoped Manifold ContDiff Bundle
noncomputable section
namespace CurveControl.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)

/-- **Math.** The model conversion from the max product to the genuine L2 product. -/
def productL2Equiv : (E × F) ≃L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm

/-- **Math.** L2 model with the same chart-target space as the ordinary product. -/
def productL2Model : ModelWithCorners ℝ (WithLp 2 (E × F)) (ModelProd H K) :=
  (I.prod J).transContinuousLinearEquiv (productL2Equiv (E := E) (F := F))

/-- **Math.** Model transport preserves the absence of boundary. -/
instance productL2_boundaryless [I.Boundaryless] [J.Boundaryless] :
    (productL2Model I J).Boundaryless where
  range_eq_univ := by
    rw [productL2Model, ModelWithCorners.transContinuousLinearEquiv_range,
      ModelWithCorners.range_eq_univ]
    simpa only [Set.image_univ] using
      (productL2Equiv (E := E) (F := F)).surjective.range_eq

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

/-- **Math.** The existing product atlas is smooth for the L2 model. -/
instance productL2_isManifold : IsManifold (productL2Model I J) ∞ (M × N) := by
  unfold productL2Model
  infer_instance

/-- **Math.** Identity on points, viewed as a diffeomorphism between the two models. -/
def productModelDiffeomorph :
    (M × N) ≃ₘ⟮I.prod J, productL2Model I J⟯ (M × N) :=
  ContinuousLinearEquiv.toTransContinuousLinearEquiv (I.prod J) (M × N)
    (productL2Equiv (E := E) (F := F))

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- **Math.** Changing the model does not change points. -/
theorem productModelDiffeomorph_apply (p : M × N) : productModelDiffeomorph I J p = p := rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [IsManifold I ∞ M] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Math.** The inverse identity diffeomorphism is a genuine smooth immersion. -/
theorem productModelInverse_immersion :
    DCSmoothImmersion (I := productL2Model I J) (I' := I.prod J)
      (productModelDiffeomorph (M := M) (N := N) I J).symm := by
  refine ⟨(productModelDiffeomorph I J).symm.contMDiff, ?_⟩
  intro p
  exact ((productModelDiffeomorph I J).symm.mfderivToContinuousLinearEquiv
    (by simp) p).injective

/-- **Math.** The actual product metric transported to the Hilbert model. -/
def productL2Metric (g : RiemannianMetric I M) (h : RiemannianMetric J N) :
    RiemannianMetric (productL2Model I J) (M × N) :=
  DCInducedMetric (DCProductMetric g h) (productModelDiffeomorph I J).symm
    (productModelInverse_immersion I J)

/-- **Math.** The transported metric is exactly pullback by the model-change derivative. -/
theorem productL2Metric_inner (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u v : TangentSpace (productL2Model I J) p) :
    (productL2Metric I J g h).inner p u v =
      (DCProductMetric g h).inner p
        (mfderiv (productL2Model I J) (I.prod J) (productModelDiffeomorph I J).symm p u)
        (mfderiv (productL2Model I J) (I.prod J) (productModelDiffeomorph I J).symm p v) := rfl

end CurveControl.Geometry
