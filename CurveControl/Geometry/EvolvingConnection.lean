import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Time-dependent connection coefficients in a fixed chart

Adapted from MorganTianLib.Ch01.CurvatureCommutation: the coefficient field may
now depend on the parameter separately from the chart point. Product rules and
Schwarz symmetry prove all commutation identities below. No curvature evolution
or commutation conclusion is assumed. This is the coordinate analytic layer;
identification with the Levi-Civita connection of a Ricci-flow metric is separate.
-/
open scoped Topology ContDiff
noncomputable section
namespace CurveControl.Geometry.EvolvingConnection
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Connection along a map, with an independently varying coefficient field. -/
def covDerivAlong (Γ : P → E →L[ℝ] E →L[ℝ] E) (u V : P → E) (d p : P) : E :=
  fderiv ℝ V p d + Γ p (fderiv ℝ u p d) (V p)

theorem covDerivAlong_def (Γ : P → E →L[ℝ] E →L[ℝ] E) (u V : P → E) (d p : P) :
    covDerivAlong Γ u V d p = fderiv ℝ V p d + Γ p (fderiv ℝ u p d) (V p) := rfl

/-- Actual derivative expansion, including the derivative of the coefficients. -/
theorem fderiv_covDerivAlong_apply {Γ : P → E →L[ℝ] E →L[ℝ] E} {u V : P → E}
    {p : P} (hu : ContDiffAt ℝ 2 u p) (hV : ContDiffAt ℝ 2 V p)
    (hΓ : DifferentiableAt ℝ Γ p) (d e : P) :
    fderiv ℝ (covDerivAlong Γ u V d) p e
      = fderiv ℝ (fderiv ℝ V) p e d
        + fderiv ℝ Γ p e (fderiv ℝ u p d) (V p)
        + Γ p (fderiv ℝ (fderiv ℝ u) p e d) (V p)
        + Γ p (fderiv ℝ u p d) (fderiv ℝ V p e) := by
  have h21 : ((1 : ℕ∞ω) + 1 : ℕ∞ω) ≤ 2 := by norm_num
  have hu1 : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  have hV1 : DifferentiableAt ℝ V p := hV.differentiableAt (by norm_num)
  have hD2u : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) p) p :=
    ((hu.fderiv_right h21).differentiableAt (by norm_num)).hasFDerivAt
  have hD2V : HasFDerivAt (fderiv ℝ V) (fderiv ℝ (fderiv ℝ V) p) p :=
    ((hV.fderiv_right h21).differentiableAt (by norm_num)).hasFDerivAt
  -- the two directional-derivative fields
  have happV : HasFDerivAt (fun q => fderiv ℝ V q d)
      ((fderiv ℝ (fderiv ℝ V) p).flip d) p := by
    have h := hD2V.clm_apply (hasFDerivAt_const d p)
    simpa using h
  have happu : HasFDerivAt (fun q => fderiv ℝ u q d)
      ((fderiv ℝ (fderiv ℝ u) p).flip d) p := by
    have h := hD2u.clm_apply (hasFDerivAt_const d p)
    simpa using h
  -- the Christoffel term, by two applications of the CLM product rule
  have hA : HasFDerivAt (fun q => Γ q (fderiv ℝ u q d))
      ((Γ p).comp ((fderiv ℝ (fderiv ℝ u) p).flip d)
        + (fderiv ℝ Γ p).flip (fderiv ℝ u p d)) p :=
    hΓ.hasFDerivAt.clm_apply happu
  have hG := hA.clm_apply hV1.hasFDerivAt
  have htot : HasFDerivAt (covDerivAlong Γ u V d)
      (((fderiv ℝ (fderiv ℝ V) p).flip d)
        + ((Γ p (fderiv ℝ u p d)).comp (fderiv ℝ V p)
          + ((Γ p).comp ((fderiv ℝ (fderiv ℝ u) p).flip d)
            + (fderiv ℝ Γ p).flip
                (fderiv ℝ u p d)).flip (V p))) p := by
    exact happV.add hG
  rw [htot.fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.flip_apply]
  abel

/-- Commutator for a parameter-dependent coefficient field. -/
theorem covDerivAlong_comm {Γ : P → E →L[ℝ] E →L[ℝ] E} {u V : P → E} {p : P}
    (hu : ContDiffAt ℝ 2 u p) (hV : ContDiffAt ℝ 2 V p)
    (hΓ : DifferentiableAt ℝ Γ p) (d₁ d₂ : P) :
    covDerivAlong Γ u (covDerivAlong Γ u V d₂) d₁ p
      - covDerivAlong Γ u (covDerivAlong Γ u V d₁) d₂ p
      = fderiv ℝ Γ p d₁ (fderiv ℝ u p d₂) (V p)
        - fderiv ℝ Γ p d₂ (fderiv ℝ u p d₁) (V p)
        + Γ p (fderiv ℝ u p d₁) (Γ p (fderiv ℝ u p d₂) (V p))
        - Γ p (fderiv ℝ u p d₂) (Γ p (fderiv ℝ u p d₁) (V p)) := by
  have h1 := fderiv_covDerivAlong_apply hu hV hΓ d₂ d₁
  have h2 := fderiv_covDerivAlong_apply hu hV hΓ d₁ d₂
  have hVs := (hV.isSymmSndFDerivAt (by simp)).eq d₂ d₁
  have hus := (hu.isSymmSndFDerivAt (by simp)).eq d₂ d₁
  rw [covDerivAlong_def Γ u (covDerivAlong Γ u V d₂) d₁ p,
    covDerivAlong_def Γ u (covDerivAlong Γ u V d₁) d₂ p, h1, h2,
    covDerivAlong_def Γ u V d₂ p, covDerivAlong_def Γ u V d₁ p]
  simp only [map_add]
  rw [hVs, hus]
  abel

/-- Torsion-free mixed velocities, without assuming mixed derivatives commute. -/
theorem covDerivAlong_fderiv_symm {Γ : P → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {p : P} (hu : ContDiffAt ℝ 2 u p)
    (hΓsymm : ∀ X Y, Γ p X Y = Γ p Y X) (d₁ d₂ : P) :
    covDerivAlong Γ u (fun q => fderiv ℝ u q d₂) d₁ p
      = covDerivAlong Γ u (fun q => fderiv ℝ u q d₁) d₂ p := by
  have h21 : ((1 : ℕ∞ω) + 1 : ℕ∞ω) ≤ 2 := by norm_num
  have hD2u : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) p) p :=
    ((hu.fderiv_right h21).differentiableAt (by norm_num)).hasFDerivAt
  have happ : ∀ d : P, fderiv ℝ (fun q => fderiv ℝ u q d) p
      = (fderiv ℝ (fderiv ℝ u) p).flip d := by
    intro d
    have h := hD2u.clm_apply (hasFDerivAt_const d p)
    have h' : HasFDerivAt (fun q => fderiv ℝ u q d)
        ((fderiv ℝ (fderiv ℝ u) p).flip d) p := by simpa using h
    exact h'.fderiv
  rw [covDerivAlong_def, covDerivAlong_def, happ d₁, happ d₂]
  simp only [ContinuousLinearMap.flip_apply]
  rw [(hu.isSymmSndFDerivAt (by simp)).eq d₁ d₂,
    hΓsymm (fderiv ℝ u p d₁) (fderiv ℝ u p d₂)]


/-- The time-first pullback of an evolving Christoffel contraction. -/
def coefficients (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E) (u : ℝ × ℝ → E)
    (p : ℝ × ℝ) : E →L[ℝ] E →L[ℝ] E := Γ p.1 (u p)

/-- Time and spatial covariant derivatives use actual Fréchet derivatives. -/
def covTime (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E) (u V : ℝ × ℝ → E) :=
  covDerivAlong (coefficients Γ u) u V (1, 0)

def covSpace (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E) (u V : ℝ × ℝ → E) :=
  covDerivAlong (coefficients Γ u) u V (0, 1)

/-- Curvature at a fixed time, computed from the spatial slice of Γ. -/
def curvature (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E) (t : ℝ) (x X Y Z : E) : E :=
  fderiv ℝ (Γ t) x X Y Z - fderiv ℝ (Γ t) x Y X Z
    + Γ t x X (Γ t x Y Z) - Γ t x Y (Γ t x X Z)

/-- Actual explicit time derivative at a fixed chart point. -/
def timeVariation (Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E) (t : ℝ) (x : E) :=
  fderiv ℝ (fun s => Γ s x) t 1

/-- Chain rule for the time-first pullback. Joint differentiability is the only
coefficient regularity hypothesis; the derivative is not prescribed as input. -/
theorem fderiv_coefficients {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u : ℝ × ℝ → E} {p : ℝ × ℝ} (hu : DifferentiableAt ℝ u p)
    (hΓ : DifferentiableAt ℝ (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p))
    (d : ℝ × ℝ) :
    fderiv ℝ (coefficients Γ u) p d =
      fderiv ℝ (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p) (d.1, fderiv ℝ u p d) := by
  have h := HasFDerivAt.comp (x := p) (g := fun z : ℝ × E => Γ z.1 z.2)
    (f := fun q : ℝ × ℝ => (q.1, u q)) hΓ.hasFDerivAt
    (hasFDerivAt_fst.prodMk hu.hasFDerivAt)
  rw [show fderiv ℝ (coefficients Γ u) p = _ from h.fderiv]
  rfl

/-- The spatial slice derivative is the joint derivative in direction `(0,X)`. -/
theorem spatial_slice_fderiv {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E} {t : ℝ} {x : E}
    (hΓ : DifferentiableAt ℝ (fun z : ℝ × E => Γ z.1 z.2) (t, x)) (X : E) :
    fderiv ℝ (Γ t) x X =
      fderiv ℝ (fun z : ℝ × E => Γ z.1 z.2) (t, x) (0, X) := by
  have h := HasFDerivAt.comp (x := x) (g := fun z : ℝ × E => Γ z.1 z.2)
    (f := fun y : E => (t, y)) hΓ.hasFDerivAt
    ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  rw [show fderiv ℝ (Γ t) x = _ from h.fderiv]
  rfl

/-- The time slice derivative is the joint derivative in direction `(1,0)`. -/
theorem time_slice_fderiv {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E} {t : ℝ} {x : E}
    (hΓ : DifferentiableAt ℝ (fun z : ℝ × E => Γ z.1 z.2) (t, x)) :
    timeVariation Γ t x =
      fderiv ℝ (fun z : ℝ × E => Γ z.1 z.2) (t, x) (1, 0) := by
  have h := HasFDerivAt.comp (x := t) (g := fun z : ℝ × E => Γ z.1 z.2)
    (f := fun s : ℝ => (s, x)) hΓ.hasFDerivAt
    ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const (𝕜 := ℝ) x t))
  unfold timeVariation
  rw [show fderiv ℝ (fun s => Γ s x) t = _ from h.fderiv]
  rfl

/-- Evolving-connection time-space commutator. The additional term is the
actual time derivative of Γ at fixed position, in addition to spatial curvature. -/
theorem covTime_covSpace_comm {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {u V : ℝ × ℝ → E} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 2 u p) (hV : ContDiffAt ℝ 2 V p)
    (hΓ : DifferentiableAt ℝ (fun z : ℝ × E => Γ z.1 z.2) (p.1, u p)) :
    covTime Γ u (covSpace Γ u V) p - covSpace Γ u (covTime Γ u V) p =
      curvature Γ p.1 (u p) (fderiv ℝ u p (1, 0)) (fderiv ℝ u p (0, 1)) (V p)
      + timeVariation Γ p.1 (u p) (fderiv ℝ u p (0, 1)) (V p) := by
  have hu1 := hu.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (coefficients Γ u) p :=
    (HasFDerivAt.comp (x := p) (g := fun z : ℝ × E => Γ z.1 z.2)
      (f := fun q : ℝ × ℝ => (q.1, u q)) hΓ.hasFDerivAt
      (hasFDerivAt_fst.prodMk hu1.hasFDerivAt)).differentiableAt
  change covDerivAlong (coefficients Γ u) u
      (covDerivAlong (coefficients Γ u) u V (0, 1)) (1, 0) p -
    covDerivAlong (coefficients Γ u) u
      (covDerivAlong (coefficients Γ u) u V (1, 0)) (0, 1) p = _
  rw [covDerivAlong_comm hu hV hA]
  rw [fderiv_coefficients hu1 hΓ, fderiv_coefficients hu1 hΓ]
  simp only [coefficients, curvature]
  rw [spatial_slice_fderiv hΓ, spatial_slice_fderiv hΓ, time_slice_fderiv hΓ]
  have hp : ((1 : ℝ), fderiv ℝ u p (1, 0)) =
      (1, 0) + (0, fderiv ℝ u p (1, 0)) := by simp
  rw [hp, map_add, add_apply, add_apply]
  abel

/-- Torsion-free identity for the actual mixed time/spatial velocities. -/
theorem covTime_spaceVelocity_eq_covSpace_timeVelocity
    {Γ : ℝ → E → E →L[ℝ] E →L[ℝ] E} {u : ℝ × ℝ → E} {p : ℝ × ℝ}
    (hu : ContDiffAt ℝ 2 u p)
    (hΓsymm : ∀ X Y, Γ p.1 (u p) X Y = Γ p.1 (u p) Y X) :
    covTime Γ u (fun q => fderiv ℝ u q (0, 1)) p =
      covSpace Γ u (fun q => fderiv ℝ u q (1, 0)) p :=
  covDerivAlong_fderiv_symm hu hΓsymm (1, 0) (0, 1)

end CurveControl.Geometry.EvolvingConnection
