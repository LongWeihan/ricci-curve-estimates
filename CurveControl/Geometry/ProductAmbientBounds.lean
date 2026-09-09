import CurveControl.Geometry.ProductIntrinsicCurvature
import CurveControl.Geometry.AmbientBounds

/-!
# Curvature and Ricci bounds independent of a one-dimensional factor

The projection lengths are bounded by the actual product metric length. Actual
intrinsic curvature/Ricci splitting and one-dimensional flatness then propagate
the original constants. Covariant Ricci differentiation is a separate module.
-/

open Riemannian MorganTianLib
open scoped Manifold ContDiff Bundle Topology

noncomputable section
set_option linter.unusedSectionVars false

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The two upstream pointwise curvature packages agree. -/
theorem ambientRm_eq_canonical (g : Riemannian.RiemannianMetric I M) (p : M)
    (x y z w : TangentSpace I p) : AmbientBounds.rm g p x y z w =
      g.leviCivitaConnection.curvatureFormAt g p x y z w := by
  unfold AmbientBounds.rm
  rw [MorganTianLib.curvatureFormAt_def,
    g.leviCivitaConnection.curvatureFormAt_eq g p
      (X := extendVector p x) (Y := extendVector p y)
      (Z := extendVector p z) (T := extendVector p w)]
  all_goals simp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [SigmaCompactSpace N] [T2Space N]

/-- **Math.** First projection decreases actual Riemannian tangent length. -/
theorem productL2_metricNorm_fst_le (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) (x : TangentSpace (productL2Model I J) p) :
    AmbientBounds.metricNorm g p.1 (productL2Equiv.symm x).1 ≤
      AmbientBounds.metricNorm (productL2Metric I J g h) p x := by
  unfold AmbientBounds.metricNorm
  rw [productL2Metric_metricInner_split]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (h.metricInner_self_nonneg _ _))

/-- **Math.** Second projection decreases actual Riemannian tangent length. -/
theorem productL2_metricNorm_snd_le (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) (x : TangentSpace (productL2Model I J) p) :
    AmbientBounds.metricNorm h p.2 (productL2Equiv.symm x).2 ≤
      AmbientBounds.metricNorm (productL2Metric I J g h) p x := by
  unfold AmbientBounds.metricNorm
  rw [productL2Metric_metricInner_split]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (g.metricInner_self_nonneg _ _))

/-- **Math.** The ambient curvature package used by curve estimates splits. -/
theorem ambientRm_productL2 (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) (x y z w : TangentSpace (productL2Model I J) p) :
    AmbientBounds.rm (productL2Metric I J g h) p x y z w =
      AmbientBounds.rm g p.1 (productL2Equiv.symm x).1 (productL2Equiv.symm y).1
        (productL2Equiv.symm z).1 (productL2Equiv.symm w).1 +
      AmbientBounds.rm h p.2 (productL2Equiv.symm x).2 (productL2Equiv.symm y).2
        (productL2Equiv.symm z).2 (productL2Equiv.symm w).2 := by
  simp only [ambientRm_eq_canonical]
  exact canonicalCurvatureFormAt_productL2 g h p x y z w

/-- **Math.** The Ricci bound propagates with precisely the same base constant
for any one-dimensional factor metric. -/
theorem productL2_ricci_bound_of_finrank_one
    (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N) (p : M × N)
    {B C D : ℝ} (hb : AmbientBounds.TensorBoundsAt g p.1 B C D)
    (hdim : Module.finrank ℝ F = 1)
    (x y : TangentSpace (productL2Model I J) p) :
    |ricciTensorAt (productL2Metric I J g h) p x y| ≤
      B * AmbientBounds.metricNorm (productL2Metric I J g h) p x *
        AmbientBounds.metricNorm (productL2Metric I J g h) p y := by
  rw [ricciTensorAt_productL2, ricciTensorAt_eq_zero_of_finrank_one hdim h, add_zero]
  calc
    _ ≤ B * AmbientBounds.metricNorm g p.1 (productL2Equiv.symm x).1 *
        AmbientBounds.metricNorm g p.1 (productL2Equiv.symm y).1 := hb.ricci _ _
    _ ≤ _ := by
      have hB := hb.ricci_nonneg
      gcongr <;> first
      | exact productL2_metricNorm_fst_le g h p _
      | (unfold AmbientBounds.metricNorm; positivity)

/-- **Math.** The full four-slot curvature bound propagates with precisely
the same base constant for any one-dimensional factor metric. -/
theorem productL2_curvature_bound_of_finrank_one
    (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N) (p : M × N)
    {B C D : ℝ} (hb : AmbientBounds.TensorBoundsAt g p.1 B C D)
    (hdim : Module.finrank ℝ F = 1)
    (x y z w : TangentSpace (productL2Model I J) p) :
    |AmbientBounds.rm (productL2Metric I J g h) p x y z w| ≤
      C * AmbientBounds.metricNorm (productL2Metric I J g h) p x *
        AmbientBounds.metricNorm (productL2Metric I J g h) p y *
        AmbientBounds.metricNorm (productL2Metric I J g h) p z *
        AmbientBounds.metricNorm (productL2Metric I J g h) p w := by
  rw [ambientRm_productL2, ambientRm_eq_canonical h,
    canonicalCurvatureFormAt_eq_zero_of_finrank_one hdim h, add_zero]
  calc
    _ ≤ C * AmbientBounds.metricNorm g p.1 (productL2Equiv.symm x).1 *
        AmbientBounds.metricNorm g p.1 (productL2Equiv.symm y).1 *
        AmbientBounds.metricNorm g p.1 (productL2Equiv.symm z).1 *
        AmbientBounds.metricNorm g p.1 (productL2Equiv.symm w).1 := hb.curvature _ _ _ _
    _ ≤ _ := by
      have hC := hb.curvature_nonneg
      gcongr <;> first
      | exact productL2_metricNorm_fst_le g h p _
      | (unfold AmbientBounds.metricNorm; positivity)

end CurveControl.Geometry

#print axioms CurveControl.Geometry.ambientRm_eq_canonical
#print axioms CurveControl.Geometry.productL2_metricNorm_fst_le
#print axioms CurveControl.Geometry.productL2_metricNorm_snd_le
#print axioms CurveControl.Geometry.ambientRm_productL2
#print axioms CurveControl.Geometry.productL2_ricci_bound_of_finrank_one
#print axioms CurveControl.Geometry.productL2_curvature_bound_of_finrank_one
