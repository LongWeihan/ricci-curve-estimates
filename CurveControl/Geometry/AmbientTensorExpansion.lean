import CurveControl.Geometry.AmbientTensorRegularity
import MorganTianLib.Ch01.CurvatureFrameBridge

/-! Finite-basis expansion of the actual ambient curvature tensors. -/
open scoped ContDiff Manifold Topology Bundle
open Set Riemannian MorganTianLib
noncomputable section
namespace CurveControl.Geometry.AmbientTensorExpansion

section LinearAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {ι : Type*} [Fintype ι]

theorem trilinear_basis_expand (L : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (b : Module.Basis ι ℝ V) (u v w : V) :
    L u v w = ∑ i, ∑ j, ∑ k,
      (b.repr u i) * (b.repr v j) * (b.repr w k) * L (b i) (b j) (b k) := by
  classical
  calc
    L u v w = L (∑ i, (b.repr u i) • b i)
        (∑ j, (b.repr v j) • b j) (∑ k, (b.repr w k) • b k) := by
      rw [b.sum_repr u, b.sum_repr v, b.sum_repr w]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        ext j
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem quadrilinear_basis_expand (L : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (b : Module.Basis ι ℝ V) (u v w z : V) :
    L u v w z = ∑ i, ∑ j, ∑ k, ∑ l,
      (b.repr u i) * (b.repr v j) * (b.repr w k) * (b.repr z l) *
        L (b i) (b j) (b k) (b l) := by
  classical
  calc
    L u v w z = L (∑ i, (b.repr u i) • b i)
        (∑ j, (b.repr v j) • b j) (∑ k, (b.repr w k) • b k)
        (∑ l, (b.repr z l) • b l) := by
      rw [b.sum_repr u, b.sum_repr v, b.sum_repr w, b.sum_repr z]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        ext k
        rw [Finset.sum_comm]
        arg 2
        ext j
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        ext j
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
end LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Currying of the actual covariant derivative of Ricci in its three slots. -/
def covRicciTrilinear (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ where
  toFun := covRicciTensorBilin g nabla hLC p
  map_add' := by
    intro u v
    ext w z
    exact covRicciAt_add_dir g nabla hLC p u v w z
  map_smul' := by
    intro a u
    ext v w
    exact covRicciAt_smul_dir g nabla hLC p a u v w

@[simp] theorem covRicciTrilinear_apply (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    (u v w : TangentSpace I p) :
    covRicciTrilinear g nabla hLC p u v w = covRicciAt g nabla hLC p u v w := rfl

/-- Works for every finite basis, in particular `chartBasisFamily α hp`. -/
theorem covRicciAt_basis_expand (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace I p))
    (u v w : TangentSpace I p) :
    covRicciAt g nabla hLC p u v w = ∑ i, ∑ j, ∑ k,
      (b.repr u i) * (b.repr v j) * (b.repr w k) *
        covRicciAt g nabla hLC p (b i) (b j) (b k) :=
  trilinear_basis_expand (covRicciTrilinear g nabla hLC p) b u v w

/-- Currying of the intrinsic upstream curvature form in its four slots. -/
def curvatureQuadrilinear (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ]
      TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ where
  toFun := fun u => {
    toFun := fun v => LinearMap.mk₂ ℝ
      (fun w z => MorganTianLib.curvatureFormAt g nabla p u v w z)
      (fun w w' z => curvatureFormAt_add_trd g nabla p u v w w' z)
      (fun a w z => curvatureFormAt_smul_trd g nabla p a u v w z)
      (fun w z z' => curvatureFormAt_add_fth g nabla p u v w z z')
      (fun a w z => curvatureFormAt_smul_fth g nabla p a u v w z)
    map_add' := by
      intro v v'
      ext w z
      exact curvatureFormAt_add_snd g nabla p u v v' w z
    map_smul' := by
      intro a v
      ext w z
      exact curvatureFormAt_smul_snd g nabla p a u v w z }
  map_add' := by
    intro u u'
    ext v w z
    exact curvatureFormAt_add_left g nabla p u u' v w z
  map_smul' := by
    intro a u
    ext v w z
    exact curvatureFormAt_smul_left g nabla p a u v w z

@[simp] theorem curvatureQuadrilinear_apply (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (u v w z : TangentSpace I p) :
    curvatureQuadrilinear g nabla p u v w z = MorganTianLib.curvatureFormAt g nabla p u v w z := rfl

theorem curvatureFormAt_basis_expand (g : Riemannian.RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace I p))
    (u v w z : TangentSpace I p) :
    MorganTianLib.curvatureFormAt g nabla p u v w z = ∑ i, ∑ j, ∑ k, ∑ l,
      (b.repr u i) * (b.repr v j) * (b.repr w k) * (b.repr z l) *
        MorganTianLib.curvatureFormAt g nabla p (b i) (b j) (b k) (b l) :=
  quadrilinear_basis_expand (curvatureQuadrilinear g nabla p) b u v w z

end CurveControl.Geometry.AmbientTensorExpansion
