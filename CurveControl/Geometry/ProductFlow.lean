import CurveControl.Geometry.ProductModel
import CurveControl.Geometry.ProductMetric
import CurveControl.Geometry.ProductIntrinsicCurvature
import MorganTianLib.Ch03.RicciFlow.Basic

/-! Time variation of the genuine product metric. The second metric is fixed
in time. Ricci splitting is a separate geometric theorem, not an assumption
that the product already solves Ricci flow. -/

open Riemannian MorganTianLib Set Filter Bundle
open scoped Manifold ContDiff Topology
noncomputable section
namespace CurveControl.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

/-- **Math.** The actual derivative of the model-change identity followed by
the base projection, on a tangent vector to the L2 product model. -/
def productBaseTangent (p : M × N) (u : TangentSpace (productL2Model I J) p) :
    TangentSpace I p.1 :=
  (mfderiv (productL2Model I J) (I.prod J) (productModelDiffeomorph I J).symm p u).1

def productFactorTangent (p : M × N) (u : TangentSpace (productL2Model I J) p) :
    TangentSpace J p.2 :=
  (mfderiv (productL2Model I J) (I.prod J) (productModelDiffeomorph I J).symm p u).2

/-- **Math.** Metric splitting through actual tangent projections. -/
theorem productL2Metric_inner_split (g : Riemannian.RiemannianMetric I M) (h : Riemannian.RiemannianMetric J N)
    (p : M × N) (u v : TangentSpace (productL2Model I J) p) :
    (productL2Metric I J g h).metricInner p u v =
      g.metricInner p.1 (productBaseTangent I J p u) (productBaseTangent I J p v) +
      h.metricInner p.2 (productFactorTangent I J p u) (productFactorTangent I J p v) := by
  exact productMetric_inner g h p _ _

omit [FiniteDimensional ℝ E] in
theorem horizontal_inCoordinates_eq (a p : M)
    (B : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) (t₀ t : ℝ)
    (hp : p ∈ (trivializationAt E (TangentSpace I) a).baseSet) :
    ContinuousLinearMap.inCoordinates E (HorizontalTangentSpace I M)
      (E →L[ℝ] ℝ) (fun z : M × ℝ => HorizontalTangentSpace I M z →L[ℝ] ℝ)
      (a, t₀) (p, t) (a, t₀) (p, t) B =
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun p : M => TangentSpace I p →L[ℝ] ℝ) a p a p B := by
  have hpH : (p, t) ∈ (trivializationAt E (HorizontalTangentSpace I M) (a, t₀)).baseSet := hp
  ext u v
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial (M × ℝ) ℝ) hpH hpH (by simp),
    inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hp hp (by simp)]
  have hs (w : E) :
      (trivializationAt E (HorizontalTangentSpace I M) (a, t₀)).symm (p, t) w =
        (trivializationAt E (TangentSpace I) a).symm p w := by
    let eH := trivializationAt E (HorizontalTangentSpace I M) (a, t₀)
    let eT := trivializationAt E (TangentSpace I) a
    apply (eT.continuousLinearEquivAt ℝ p hp).injective
    change (eT ⟨p, eH.symm (p,t) w⟩).2 = (eT ⟨p, eT.symm p w⟩).2
    have heH_apply (z : HorizontalTangentSpace I M (p,t)) :
        (eH ⟨(p,t), z⟩).2 = (eT ⟨p, z⟩).2 := by
      let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
      change ((@trivializationAt (M × ℝ) E _ _
        ((f : M × ℝ → M) *ᵖ (TangentSpace I : M → Type _))
        (Pullback.TotalSpace.topologicalSpace E (TangentSpace I) f) _
        (FiberBundle.pullback f) (a, t₀)) ⟨(p,t), z⟩).2 = _
      rfl
    rw [← heH_apply]
    exact (congrArg Prod.snd (eH.apply_mk_symm hpH w)).trans
      (congrArg Prod.snd (eT.apply_mk_symm hp w)).symm
  have htH : trivializationAt ℝ (Bundle.Trivial (M × ℝ) ℝ) (a,t₀) =
      Bundle.Trivial.trivialization (M × ℝ) ℝ := Bundle.Trivial.eq_trivialization _ _ _
  have htM : trivializationAt ℝ (Bundle.Trivial M ℝ) a =
      Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization _ _ _
  simp only [htH, htM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply, hs]

omit [FiniteDimensional ℝ E] in
/-- **Math.** A static metric gives a jointly smooth family on every time set. -/
theorem isSmoothMetricFamilyOn_const (g : Riemannian.RiemannianMetric I M) (T : Set ℝ) :
    IsSmoothMetricFamilyOn (fun _ => g) T := by
  intro z hz
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_id, ?_⟩
  have hg := ((contMDiffAt_hom_bundle _).mp (g.contMDiff z.1)).2
  have hf : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞ (Prod.fst : M × ℝ → M) z := contMDiffAt_fst
  have hcomp := hg.comp z hf
  apply hcomp.contMDiffWithinAt.congr_of_eventuallyEq
  have hevent : ∀ᶠ w : M × ℝ in 𝓝 z,
      w.1 ∈ (trivializationAt E (TangentSpace I) z.1).baseSet :=
    continuousAt_fst ((trivializationAt E (TangentSpace I) z.1).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) z.1))
  exact (hevent.mono fun w hw =>
    horizontal_inCoordinates_eq I z.1 w.1 (g.inner w.1) z.2 w.2 hw).filter_mono nhdsWithin_le_nhds
  exact horizontal_inCoordinates_eq I z.1 z.1 (g.inner z.1) z.2 z.2
    (mem_baseSet_trivializationAt _ _ _)

omit [FiniteDimensional ℝ E] in
theorem metricFamily_coordinates {g : ℝ → Riemannian.RiemannianMetric I M} {T : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g T) (z : M × ℝ) (hz : z.2 ∈ T) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun w : M × ℝ => ContinuousLinearMap.inCoordinates E (TangentSpace I)
        (E →L[ℝ] ℝ) (fun p : M => TangentSpace I p →L[ℝ] ℝ)
        z.1 w.1 z.1 w.1 ((g w.2).inner w.1)) (univ ×ˢ T) z := by
  have hc := ((contMDiffWithinAt_hom_bundle _).mp (hg z ⟨mem_univ _, hz⟩)).2
  apply hc.congr_of_eventuallyEq
  have hevent : ∀ᶠ w : M × ℝ in 𝓝 z,
      w.1 ∈ (trivializationAt E (TangentSpace I) z.1).baseSet :=
    continuousAt_fst ((trivializationAt E (TangentSpace I) z.1).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) z.1))
  exact (hevent.mono fun w hw =>
    (horizontal_inCoordinates_eq I z.1 w.1 ((g w.2).inner w.1) z.2 w.2 hw).symm).filter_mono
      nhdsWithin_le_nhds
  exact (horizontal_inCoordinates_eq I z.1 z.1 ((g z.2).inner z.1) z.2 z.2
    (mem_baseSet_trivializationAt _ _ _)).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Math.** Pullback of a jointly smooth metric family by a fixed smooth map
is a jointly smooth bilinear-form section, without assuming the map immerses.
This adapts DoCarmo `DCInducedForm_contMDiff` to horizontal time-space bundles. -/
theorem contMDiffOn_timePullbackForm {g : ℝ → Riemannian.RiemannianMetric I M} {T : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g T) {f : N → M} (hf : ContMDiff J I ∞ f) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ))
      ((J.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun z : N × ℝ => (⟨z, DCInducedForm (g z.2) f z.1⟩ :
        TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
          (fun z : N × ℝ => HorizontalTangentSpace J N z →L[ℝ]
            HorizontalTangentSpace J N z →L[ℝ] ℝ))) (univ ×ˢ T) := by
  intro z₀ hz₀
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_id, ?_⟩
  let sT := trivializationAt F (TangentSpace J) z₀.1
  let tT := trivializationAt E (TangentSpace I) (f z₀.1)
  let D := inTangentCoordinates J I id f (fun x => mfderiv J I f x) z₀.1
  let G : M × ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun w =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun p : M => TangentSpace I p →L[ℝ] ℝ)
      (f z₀.1) w.1 (f z₀.1) w.1 ((g w.2).inner w.1)
  have hD : ContMDiffAt J 𝓘(ℝ, F →L[ℝ] E) ∞ D z₀.1 :=
    hf.contMDiffAt.mfderiv_const (by simp)
  have hfst : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) J ∞ (Prod.fst : N × ℝ → N) z₀ := contMDiffAt_fst
  have hDs := (hD.comp z₀ hfst).contMDiffWithinAt (s := univ ×ˢ T)
  have hmap : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : N × ℝ => (f z.1, z.2)) :=
    (hf.comp contMDiff_fst).prodMk contMDiff_snd
  have hmaps : MapsTo (fun z : N × ℝ => (f z.1, z.2)) (univ ×ˢ T) (univ ×ˢ T) :=
    fun z hz => ⟨mem_univ _, hz.2⟩
  have hG : ContMDiffWithinAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun z : N × ℝ => G (f z.1,z.2)) (univ ×ˢ T) z₀ :=
    (metricFamily_coordinates I hg (f z₀.1, z₀.2) hz₀.2).comp z₀
      hmap.contMDiffAt.contMDiffWithinAt hmaps
  have hΨ : ContMDiffWithinAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun z : N × ℝ => ((D z.1).precomp ℝ).comp ((G (f z.1, z.2)).comp (D z.1)))
      (univ ×ˢ T) z₀ :=
    (ContMDiffWithinAt.clm_precomp (F₃ := ℝ) hDs).clm_comp (hG.clm_comp hDs)
  apply hΨ.congr_of_eventuallyEq_of_mem _ hz₀
  have hs : ∀ᶠ z : N × ℝ in 𝓝 z₀, z.1 ∈ sT.baseSet :=
    continuousAt_fst (sT.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
  have ht : ∀ᶠ z : N × ℝ in 𝓝 z₀, f z.1 ∈ tT.baseSet :=
    (hf.continuous.continuousAt.comp continuousAt_fst)
      (tT.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [hs, ht] with z hsz htz
  change ContinuousLinearMap.inCoordinates F (HorizontalTangentSpace J N)
    (F →L[ℝ] ℝ) (fun w : N × ℝ => HorizontalTangentSpace J N w →L[ℝ] ℝ)
    z₀ z z₀ z (DCInducedForm (g z.2) f z.1) = _
  rw [horizontal_inCoordinates_eq J z₀.1 z.1 _ z₀.2 z.2 hsz]
  ext u v
  have hkey (w : F) : tT.symm (f z.1) (D z.1 w) = mfderiv J I f z.1 (sT.symm z.1 w) := by
    have hDu : D z.1 w = tT.continuousLinearEquivAt ℝ (f z.1) htz
        (mfderiv J I f z.1 ((sT.continuousLinearEquivAt ℝ z.1 hsz).symm w)) := by
      simp only [D, inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hsz htz]
      rfl
    have hcoeT : (tT.symm (f z.1) : E → TangentSpace I (f z.1)) =
        ⇑(tT.continuousLinearEquivAt ℝ (f z.1) htz).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT htz]
      funext y
      exact (tT.symmL_apply htz y).symm
    have hcoeS : (sT.symm z.1 : F → TangentSpace J z.1) =
        ⇑(sT.continuousLinearEquivAt ℝ z.1 hsz).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hsz]
      funext y
      exact (sT.symmL_apply hsz y).symm
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  change _ = G (f z.1,z.2) (D z.1 u) (D z.1 v)
  dsimp only [G]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial N ℝ) hsz hsz (by simp),
    inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) htz htz (by simp)]
  have htM : trivializationAt ℝ (Bundle.Trivial M ℝ) (f z₀.1) =
      Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization _ _ _
  have htN : trivializationAt ℝ (Bundle.Trivial N ℝ) z₀.1 =
      Bundle.Trivial.trivialization N ℝ := Bundle.Trivial.eq_trivialization _ _ _
  simp only [htM, htN, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply,
    DCInducedForm_apply, ← show sT = trivializationAt F (TangentSpace J) z₀.1 from rfl,
    ← show tT = trivializationAt E (TangentSpace I) (f z₀.1) from rfl, hkey]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- **Math.** The base projection is smooth for the genuine L2 product model. -/
theorem contMDiff_productL2_fst :
    ContMDiff (productL2Model I J) I ∞ (Prod.fst : M × N → M) := by
  exact contMDiff_fst.comp (productModelDiffeomorph I J).symm.contMDiff

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem contMDiff_productL2_snd :
    ContMDiff (productL2Model I J) J ∞ (Prod.snd : M × N → N) := by
  exact contMDiff_snd.comp (productModelDiffeomorph I J).symm.contMDiff

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem productBaseTangent_eq_mfderiv (p : M × N) (u : TangentSpace (productL2Model I J) p) :
    productBaseTangent I J p u = mfderiv (productL2Model I J) I Prod.fst p u := by
  change _ = mfderiv (productL2Model I J) I
    (Prod.fst ∘ (productModelDiffeomorph I J).symm) p u
  rw [mfderiv_comp p mdifferentiableAt_fst
    ((productModelDiffeomorph I J).symm.contMDiff.mdifferentiable (by simp) p), mfderiv_fst]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem productFactorTangent_eq_mfderiv (p : M × N) (u : TangentSpace (productL2Model I J) p) :
    productFactorTangent I J p u = mfderiv (productL2Model I J) J Prod.snd p u := by
  change _ = mfderiv (productL2Model I J) J
    (Prod.snd ∘ (productModelDiffeomorph I J).symm) p u
  rw [mfderiv_comp p mdifferentiableAt_snd
    ((productModelDiffeomorph I J).symm.contMDiff.mdifferentiable (by simp) p), mfderiv_snd]
  rfl

/-- **Math.** Joint smoothness of the genuine L2 product metric follows from
the given base family and the static factor metric, by smooth pullback and sum. -/
theorem isSmoothMetricFamilyOn_productL2 {g : ℝ → Riemannian.RiemannianMetric I M}
    {T : Set ℝ} (hg : IsSmoothMetricFamilyOn g T) (h : Riemannian.RiemannianMetric J N) :
    IsSmoothMetricFamilyOn (fun t => productL2Metric I J (g t) h) T := by
  have hb := contMDiffOn_timePullbackForm I (productL2Model I J) hg
    (contMDiff_productL2_fst I J (M := M) (N := N))
  have hf := contMDiffOn_timePullbackForm J (productL2Model I J)
    (isSmoothMetricFamilyOn_const J h T) (contMDiff_productL2_snd I J (M := M) (N := N))
  have hs := hb.add_section hf
  apply hs.congr
  intro z hz
  apply congrArg (fun B => (⟨z, B⟩ : TotalSpace (WithLp 2 (E × F) →L[ℝ]
    WithLp 2 (E × F) →L[ℝ] ℝ) (fun z : (M × N) × ℝ =>
      HorizontalTangentSpace (productL2Model I J) (M × N) z →L[ℝ]
      HorizontalTangentSpace (productL2Model I J) (M × N) z →L[ℝ] ℝ)))
  ext u v
  change (productL2Metric I J (g z.2) h).metricInner z.1 u v =
    DCInducedForm (g z.2) Prod.fst z.1 u v + DCInducedForm h Prod.snd z.1 u v
  rw [productL2Metric_inner_split, DCInducedForm_apply, DCInducedForm_apply,
    productBaseTangent_eq_mfderiv, productBaseTangent_eq_mfderiv,
    productFactorTangent_eq_mfderiv, productFactorTangent_eq_mfderiv]

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Fixed-vector time variation of the genuine product. This proves
the base Ricci term directly from the base flow equation; no product Ricci
tensor identity is used here. The within derivative includes time endpoints. -/
theorem hasDerivWithinAt_productL2Metric_of_ricciFlow
    {g : ℝ → Riemannian.RiemannianMetric I M} {T : Set ℝ} (hg : IsRicciFlowOn g T)
    (h : Riemannian.RiemannianMetric J N) {t : ℝ} (ht : t ∈ T)
    (p : M × N) (u v : TangentSpace (productL2Model I J) p) :
    HasDerivWithinAt (fun s => (productL2Metric I J (g s) h).metricInner p u v)
      (-2 * ricciTensorAt (g t) p.1 (productBaseTangent I J p u) (productBaseTangent I J p v)) T t := by
  have hd := (hg.equation t ht p.1 (productBaseTangent I J p u)
    (productBaseTangent I J p v)).add_const
      (h.metricInner p.2 (productFactorTangent I J p u) (productFactorTangent I J p v))
  simpa only [productL2Metric_inner_split] using hd

variable [NeZero (Module.finrank ℝ F)] [J.Boundaryless] [SigmaCompactSpace N] [T2Space N]

/-- **Math.** Product with any static one-dimensional Riemannian metric is
an actual jointly smooth Ricci flow, including the within equations at time
endpoints. Product Ricci splitting and one-dimensional Ricci vanishing are
proved dependencies, not assumptions of this theorem. -/
theorem isRicciFlowOn_productL2_oneDimensional
    {g : ℝ → Riemannian.RiemannianMetric I M} {T : Set ℝ}
    (hg : IsRicciFlowOn g T) (h : Riemannian.RiemannianMetric J N)
    (hdim : Module.finrank ℝ F = 1) :
    IsRicciFlowOn (fun t => productL2Metric I J (g t) h) T := by
  refine ⟨hg.ordConnected, hg.nontrivial, isSmoothMetricFamilyOn_productL2 I J hg.smooth h, ?_⟩
  intro t ht p u v
  have hd := hasDerivWithinAt_productL2Metric_of_ricciFlow I J hg h ht p u v
  have hproj (w : TangentSpace (productL2Model I J) p) :
      productBaseTangent I J p w = (productL2Equiv.symm w).1 := by
    unfold productBaseTangent
    rw [productModelInverse_mfderiv]
    rfl
  rw [hproj u, hproj v] at hd
  rw [ricciTensorAt_productL2,
    ricciTensorAt_eq_zero_of_finrank_one hdim h, add_zero]
  exact hd

end CurveControl.Geometry
