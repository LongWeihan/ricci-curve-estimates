import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1

/-!
# Genuine smooth product metric and projection estimates

We reuse DoCarmo's `DCProductMetric`, constructed as the sum of the pullbacks
along the two smooth projections. Its positive definiteness and smoothness in
the actual tangent-bundle trivializations are proved upstream, not assumed here.
The tangent space is that of the product model `I.prod J`, not an auxiliary
bundle with a stipulated splitting. No curvature or connection splitting is
claimed. The construction permits any finite-dimensional second factor and
any of its Riemannian metrics, including scaled circle metrics.
-/

open Riemannian
open scoped ContDiff Manifold Topology

noncomputable section

namespace CurveControl.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

/-- **Math.** Length of an actual tangent vector in a specified Riemannian metric. -/
def metricVectorLength (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : ℝ := Real.sqrt (g.metricInner p v v)

theorem metricVectorLength_nonneg (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : 0 ≤ metricVectorLength g p v := Real.sqrt_nonneg _

theorem metricVectorLength_sq (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : (metricVectorLength g p v) ^ 2 = g.metricInner p v v :=
  Real.sq_sqrt (g.metricInner_self_nonneg p v)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Math.** The smooth positive-definite metric on the real product manifold. -/
def productMetric (g : RiemannianMetric I M) (h : RiemannianMetric J N) :
    RiemannianMetric (I.prod J) (M × N) := DCProductMetric g h

/-- **Math.** Metric splitting evaluated on the genuine product tangent space. -/
theorem productMetric_inner (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u v : TangentSpace (I.prod J) p) :
    (productMetric g h).metricInner p u v =
      g.metricInner p.1 u.1 v.1 + h.metricInner p.2 u.2 v.2 := by
  change DCProductForm g h p u v = _
  simp only [DCProductForm, add_apply, DCInducedForm_apply,
    mfderiv_fst, mfderiv_snd]
  rfl

/-- **Math.** The square of product length is the sum of the squared factor lengths. -/
theorem productMetric_length_sq (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u : TangentSpace (I.prod J) p) :
    (metricVectorLength (productMetric g h) p u) ^ 2 =
      (metricVectorLength g p.1 u.1) ^ 2 + (metricVectorLength h p.2 u.2) ^ 2 := by
  simp only [metricVectorLength_sq, productMetric_inner]

/-- **Math.** First projection is length decreasing, uniformly in the second-factor metric. -/
theorem productMetric_fst_length_le (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u : TangentSpace (I.prod J) p) :
    metricVectorLength g p.1 u.1 ≤ metricVectorLength (productMetric g h) p u := by
  unfold metricVectorLength
  rw [productMetric_inner]
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_right (h.metricInner_self_nonneg p.2 u.2)

/-- **Math.** Second projection is length decreasing, uniformly in the first-factor metric. -/
theorem productMetric_snd_length_le (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u : TangentSpace (I.prod J) p) :
    metricVectorLength h p.2 u.2 ≤ metricVectorLength (productMetric g h) p u := by
  unfold metricVectorLength
  rw [productMetric_inner]
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_left (g.metricInner_self_nonneg p.1 u.1)

/-- **Math.** The first projection estimate explicitly in terms of its manifold differential. -/
theorem productMetric_mfderiv_fst_length_le
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u : TangentSpace (I.prod J) p) :
    metricVectorLength g p.1 (mfderiv (I.prod J) I Prod.fst p u) ≤
      metricVectorLength (productMetric g h) p u := by
  rw [mfderiv_fst]
  exact productMetric_fst_length_le g h p u

/-- **Math.** The second projection estimate explicitly in terms of its manifold differential. -/
theorem productMetric_mfderiv_snd_length_le
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (p : M × N) (u : TangentSpace (I.prod J) p) :
    metricVectorLength h p.2 (mfderiv (I.prod J) J Prod.snd p u) ≤
      metricVectorLength (productMetric g h) p u := by
  rw [mfderiv_snd]
  exact productMetric_snd_length_le g h p u

end CurveControl.Geometry

#print axioms CurveControl.Geometry.productMetric
#print axioms CurveControl.Geometry.metricVectorLength_nonneg
#print axioms CurveControl.Geometry.metricVectorLength_sq
#print axioms CurveControl.Geometry.productMetric_inner
#print axioms CurveControl.Geometry.productMetric_length_sq
#print axioms CurveControl.Geometry.productMetric_fst_length_le
#print axioms CurveControl.Geometry.productMetric_snd_length_le
#print axioms CurveControl.Geometry.productMetric_mfderiv_fst_length_le
#print axioms CurveControl.Geometry.productMetric_mfderiv_snd_length_le
