import CurveControl.Geometry.Basic
import CurveControl.Geometry.RicciConnectionVariation

/-!
# Intrinsic ambient tensor bounds and their curve evaluations

The norms in these bounds are explicitly computed from the evolving metric.
They are not the fixed model-space norm. The constants bound the actual
canonical Ricci tensor, curvature form, and covariant derivative of Ricci.
Compactness-based existence of uniform constants is a separate obligation.
-/
open scoped ContDiff Manifold Topology Bundle
open Set Filter Riemannian MorganTianLib
noncomputable section
set_option linter.unusedSectionVars false
namespace CurveControl.Geometry.AmbientBounds

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The norm induced by the actual metric on this tangent fiber. -/
def metricNorm (g : Riemannian.RiemannianMetric I M) (p : M) (v : TangentSpace I p) : ℝ :=
  Real.sqrt (g.metricInner p v v)

theorem metricNorm_nonneg (g : Riemannian.RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    0 ≤ metricNorm g p v := Real.sqrt_nonneg _

theorem metricNorm_sq (g : Riemannian.RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    metricNorm g p v ^ 2 = g.metricInner p v v :=
  Real.sq_sqrt (g.metricInner_self_nonneg p v)

theorem metricNorm_unit (g : Riemannian.RiemannianMetric I M) {p : M} {v : TangentSpace I p}
    (hv : g.metricInner p v v = 1) : metricNorm g p v = 1 := by
  simp only [metricNorm, hv, Real.sqrt_one]

/-- **Math.** The canonical Levi-Civita covariant derivative of Ricci, without
an independent tensor or connection supplied by the caller. -/
def covRic (g : Riemannian.RiemannianMetric I M) (p : M)
    (u v w : TangentSpace I p) : ℝ :=
  covRicciAt g g.leviCivitaConnection
    (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)) p u v w

/-- **Math.** The actual canonical curvature four-form, in upstream slot order. -/
def rm (g : Riemannian.RiemannianMetric I M) (p : M)
    (u v w z : TangentSpace I p) : ℝ :=
  curvatureFormAt g g.leviCivitaConnection p u v w z

/-- **Math.** Intrinsic multilinear tensor evaluation bounds at one point.
Every slot is measured with `g`, not with the model inner product. These are
ambient hypotheses only; none of the curve evolution conclusions is a field. -/
structure TensorBoundsAt (g : Riemannian.RiemannianMetric I M) (p : M)
    (B K D : ℝ) : Prop where
  ricci_nonneg : 0 ≤ B
  curvature_nonneg : 0 ≤ K
  covRic_nonneg : 0 ≤ D
  ricci : ∀ u v : TangentSpace I p,
    |ricciTensorAt g p u v| ≤ B * metricNorm g p u * metricNorm g p v
  curvature : ∀ u v w z : TangentSpace I p,
    |rm g p u v w z| ≤ K * metricNorm g p u * metricNorm g p v *
      metricNorm g p w * metricNorm g p z
  covRic : ∀ u v w : TangentSpace I p,
    |AmbientBounds.covRic g p u v w| ≤ D * metricNorm g p u * metricNorm g p v *
      metricNorm g p w

/-- **Math.** A single set of constants controls all spatial points and times. -/
def UniformTensorBoundsOn (g : ℝ → Riemannian.RiemannianMetric I M) (J : Set ℝ)
    (B K D : ℝ) : Prop := ∀ t ∈ J, ∀ p, TensorBoundsAt (g t) p B K D

namespace TensorBoundsAt
variable {g : Riemannian.RiemannianMetric I M} {p : M} {B K D : ℝ}
  (h : TensorBoundsAt g p B K D)
include h

theorem ricci_unit {S : TangentSpace I p} (hS : g.metricInner p S S = 1) :
    |ricciTensorAt g p S S| ≤ B := by
  simpa only [metricNorm_unit g hS, mul_one] using h.ricci S S

theorem ricci_diagonal (V : TangentSpace I p) :
    |ricciTensorAt g p V V| ≤ B * metricNorm g p V ^ 2 := by
  simpa only [pow_two, mul_assoc] using h.ricci V V

theorem rm_unit {S : TangentSpace I p} (hS : g.metricInner p S S = 1)
    (V : TangentSpace I p) :
    |rm g p V S V S| ≤ K * metricNorm g p V ^ 2 := by
  simpa only [metricNorm_unit g hS, mul_one, pow_two, mul_assoc] using h.curvature V S V S

theorem covRic_unit_unit {S : TangentSpace I p} (hS : g.metricInner p S S = 1)
    (V : TangentSpace I p) :
    |AmbientBounds.covRic g p S S V| ≤ D * metricNorm g p V := by
  simpa only [metricNorm_unit g hS, mul_one] using h.covRic S S V

theorem covRic_unit_last {S : TangentSpace I p} (hS : g.metricInner p S S = 1)
    (V : TangentSpace I p) :
    |AmbientBounds.covRic g p V S S| ≤ D * metricNorm g p V := by
  simpa only [metricNorm_unit g hS, mul_one] using h.covRic V S S

/-- **Math.** The quadratic ambient contribution in the squared-curvature
identity is bounded by `(6B+2K) k²`. -/
theorem quadratic_error {S : TangentSpace I p} (hS : g.metricInner p S S = 1)
    (V : TangentSpace I p) :
    |4 * metricNorm g p V ^ 2 * ricciTensorAt g p S S -
      2 * ricciTensorAt g p V V + 2 * rm g p V S V S| ≤
      (6 * B + 2 * K) * metricNorm g p V ^ 2 := by
  have h1 : |4 * metricNorm g p V ^ 2 * ricciTensorAt g p S S| ≤
      4 * metricNorm g p V ^ 2 * B := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (h.ricci_unit hS) (mul_nonneg (by norm_num) (sq_nonneg _))
  have h2 : |2 * ricciTensorAt g p V V| ≤ 2 * (B * metricNorm g p V ^ 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (h.ricci_diagonal V) (by norm_num)
  have h3 : |2 * rm g p V S V S| ≤ 2 * (K * metricNorm g p V ^ 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (h.rm_unit hS V) (by norm_num)
  calc
    _ ≤ |4 * metricNorm g p V ^ 2 * ricciTensorAt g p S S - 2 * ricciTensorAt g p V V| +
        |2 * rm g p V S V S| := abs_add_le _ _
    _ ≤ (|4 * metricNorm g p V ^ 2 * ricciTensorAt g p S S| +
        |2 * ricciTensorAt g p V V|) + |2 * rm g p V S V S| :=
      add_le_add (by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (4 * metricNorm g p V ^ 2 * ricciTensorAt g p S S) (0 : ℝ)
            (2 * ricciTensorAt g p V V))) le_rfl
    _ ≤ (4 * metricNorm g p V ^ 2 * B + 2 * (B * metricNorm g p V ^ 2)) +
        2 * (K * metricNorm g p V ^ 2) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- **Math.** The covariant-Ricci contribution is linear in curvature norm. -/
theorem linear_error {S : TangentSpace I p} (hS : g.metricInner p S S = 1)
    (V : TangentSpace I p) :
    |-4 * AmbientBounds.covRic g p S S V + 2 * AmbientBounds.covRic g p V S S| ≤
      6 * D * metricNorm g p V := by
  calc
    _ ≤ |-4 * AmbientBounds.covRic g p S S V| + |2 * AmbientBounds.covRic g p V S S| := abs_add_le _ _
    _ = 4 * |AmbientBounds.covRic g p S S V| + 2 * |AmbientBounds.covRic g p V S S| := by
      simp only [abs_mul]; norm_num
    _ ≤ 4 * (D * metricNorm g p V) + 2 * (D * metricNorm g p V) :=
      add_le_add (mul_le_mul_of_nonneg_left (h.covRic_unit_unit hS V) (by norm_num))
        (mul_le_mul_of_nonneg_left (h.covRic_unit_last hS V) (by norm_num))
    _ = _ := by ring
end TensorBoundsAt

/-- **Math.** The tensor metric norm of the actual curve curvature vector is k. -/
theorem metricNorm_curvatureVector (g : Riemannian.RiemannianMetric I M)
    (γ : ℝ → M) (x : ℝ) :
    metricNorm g (γ x) (curvatureVector g γ x) = curvature g γ x := rfl

/-- **Math.** Intrinsic environmental tensor bounds evaluated on the actual
unit tangent and actual curvature vector of an immersed curve. -/
theorem curve_evaluations {g : Riemannian.RiemannianMetric I M} (γ : ℝ → M) (x : ℝ)
    {B K D : ℝ} (h : TensorBoundsAt g (γ x) B K D)
    (himm : curveVelocity (I := I) γ x ≠ 0) :
    let S := unitTangent g γ x
    let V := curvatureVector g γ x
    |ricciTensorAt g (γ x) S S| ≤ B ∧
    |ricciTensorAt g (γ x) V V| ≤ B * curvature g γ x ^ 2 ∧
    |rm g (γ x) V S V S| ≤ K * curvature g γ x ^ 2 ∧
    |covRic g (γ x) S S V| ≤ D * curvature g γ x ∧
    |covRic g (γ x) V S S| ≤ D * curvature g γ x := by
  have hS := unitTangent_unit g γ x himm
  exact ⟨h.ricci_unit hS, h.ricci_diagonal _, h.rm_unit hS _,
    h.covRic_unit_unit hS _, h.covRic_unit_last hS _⟩

/-- **Math.** The actual curve's ambient q-evolution error, with constants
independent of the selected curve whenever the ambient tensor bounds are. -/
theorem curve_ambient_error {g : Riemannian.RiemannianMetric I M} (γ : ℝ → M) (x : ℝ)
    {B K D : ℝ} (h : TensorBoundsAt g (γ x) B K D)
    (himm : curveVelocity (I := I) γ x ≠ 0) :
    let S := unitTangent g γ x
    let V := curvatureVector g γ x
    |(4 * curvatureSq g γ x * ricciTensorAt g (γ x) S S -
        2 * ricciTensorAt g (γ x) V V + 2 * rm g (γ x) V S V S) +
      (-4 * covRic g (γ x) S S V + 2 * covRic g (γ x) V S S)| ≤
      (6 * B + 2 * K) * curvatureSq g γ x + 6 * D * curvature g γ x := by
  dsimp only
  have hS := unitTangent_unit g γ x himm
  have hq := h.quadratic_error hS (curvatureVector g γ x)
  have hl := h.linear_error hS (curvatureVector g γ x)
  simp only [metricNorm_curvatureVector, curvature_sq] at hq hl
  exact (abs_add_le _ _).trans (add_le_add hq hl)

/-- **Math.** Restricting the time domain preserves the same ambient constants. -/
theorem UniformTensorBoundsOn.mono {g : ℝ → Riemannian.RiemannianMetric I M}
    {J J' : Set ℝ} {B K D : ℝ} (h : UniformTensorBoundsOn g J B K D) (hJ : J' ⊆ J) :
    UniformTensorBoundsOn g J' B K D := fun t ht p => h t (hJ ht) p

end CurveControl.Geometry.AmbientBounds

#print axioms CurveControl.Geometry.AmbientBounds.curve_evaluations
#print axioms CurveControl.Geometry.AmbientBounds.TensorBoundsAt.quadratic_error
#print axioms CurveControl.Geometry.AmbientBounds.TensorBoundsAt.linear_error

#print axioms CurveControl.Geometry.AmbientBounds.curve_ambient_error
