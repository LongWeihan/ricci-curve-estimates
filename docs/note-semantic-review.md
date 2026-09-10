# Paper draft: independent mathematical semantic review

Date: 2026-09-09. Reviewer: curve_control_specification, not the author of this draft. Read-only review of the TeX, bibliography, mapped Lean declarations and the new example interface. Only this review file was written. No PDF typography/visual acceptance is implied.

Reviewed snapshots:

- `paper/curve-estimates.tex`: SHA-256 `776545ad532ed9361bfc0ac08af21c8cb1e742faa6154ae94c46ed195ad3a036`.
- `paper/references.bib`: SHA-256 `a8fa44c3327e713be446f9b7962a2d9ab2b4e5432282fa9bfb7f4c0e0f87358e`.
- New `CurveControl/Examples/StaticFactorApplication.lean` inspected for its paper-facing statement only: SHA-256 `4f282888c9e432a824dd6bed822e73359fb6c70623a44cd7049edc9987e4b141`. Another agent owns its independent proof acceptance.

Verdict: the main mathematical argument and relation to the Lean roots are sound. Make the two required corrections below before accepting the paper text. Neither requires a change to the main theorem or existing mathematical proofs.

## Required corrections

### R1. Update the now-obsolete scaled-factor limitation

Locations: lines 116–120 and especially lines 399–405 (“construction of concrete circle atlases or scaled factor objects”). The latter is now false of the expanded artifact. The new example constructs an actual Riemannian metric from an arbitrary supplied h₀ and proves its λ² bilinear formula and λ tangent-norm formula. It still does not construct a particular AddCircle atlas or h₀ on such an atlas.

Minimal replacement for lines 116–120:

> The supplied one-dimensional manifold may in particular be a smooth circle. The example module now constructs the genuine metric (h_lambda=lambda^2h_*) from any supplied smooth Riemannian metric (h_*), proves (|V|_{h_lambda}=lambda|V|_{h_*}), and instantiates the uniform theorem simultaneously for all positive scales. A particular AddCircle atlas and its starting metric are still caller inputs; the example does not construct curve-flow solutions or ramps.

Add mappings (all in `CurveControl/Examples/StaticFactorApplication.lean`):

- `CurveControl.Examples.StaticFactorApplication.scaledFactorMetric`
- `CurveControl.Examples.StaticFactorApplication.scaledFactorMetric_inner`
- `CurveControl.Examples.StaticFactorApplication.scaledFactorMetric_norm`
- `CurveControl.Examples.StaticFactorApplication.exists_scaledFactor_curve_bounds`

One or two combined declaration blocks are enough; no need to list every helper. If adding a full-interval constant corollary, map `CurveControl.Examples.StaticFactorApplication.exists_scaledFactor_fullInterval_bounds`, whose right sides use exp(B(b−a)) and exp(C(b−a)). Do not call it an existence theorem for ramps.

Minimal replacement for the limitations list: change “construction of concrete circle atlases or scaled factor objects” to “construction of concrete circle atlases and their starting metrics”. The new example chooses B,C before h₀ itself, so the prose may retain the stronger independence claim.

### R2. Fix the appendix's compressed final quantifier

Location: final display in Appendix A, currently `\forall\ell,i,t\in[a,b]`. Literally this quantifies the factor and curve indices over the time interval, although they are arbitrary types. The main theorem has the correct quantifiers; the displayed summary should match it.

Replace with:

    \forall\ell\in\Lambda\;\forall i\in\mathcal I\;\forall t\in[a,b]

or with `\forall\ell\;\forall i\;\forall t\in[a,b]` after explicitly specifying the index types in that display. This is a presentation correction to the mathematical statement, not a Lean defect.

## Accepted mathematical content

1. **Main theorem and constants.** Compact base M, fixed genuine one-dimensional N, a nondegenerate closed interval and actual smooth flows correctly reproduce the final roots. The existence of B,C precedes both index types, the entire h family, all curves and initial bounds. The text correctly distinguishes the fixed N/model context from witnesses constructed solely from g and the time interval. No compactness of N or regularity in indices is silently needed. Initial bounds remain explicit. Empty indices are allowed.

2. **Actual geometry and self-intersections.** X, v, S, H, q, k, L, Θ and E are defined consistently with Basic. Period-one real parameters and integration over [0,1] give the curve measure. Immersed means actual c_x nonzero. Fixed valid chart germs, not global charts or embedded curves, justify the covariant computations.

3. **Time and regularity.** Within flow equations are explicitly stated. High-order evolution is restricted to interior J, while closed continuity supplies endpoint comparison. The appendix correctly notes that IsRicciFlowOn imposes nontriviality, so [a,b] as its whole time domain cannot be a singleton. The lower-level estimate can still use a=b as a subinterval of a larger J. No accidental initial two-sided derivative is required.

4. **Moving metric, A, and curvature sign.** The product rule includes the separate −2Ric(V,W). A is ∂tΓ at fixed spatial coordinates and its lowering has the −−+ covariant-Ricci signs. The R⁻/R⁺ conversion and final rm(H,S,H,S) contraction are correct. P is the spatial projection; the explanation of its distinction from the spacetime projection is consistent with the earlier independent derivation. The actual q_t display has all five ambient error terms and the correct −4/+2 connection-gradient coefficients.

5. **Regularized PDE and comparison.** The bound (6B+2K)q+6D√q and A₀=max(...) is correct. Kato controls the regularized derivative; k³ is the actual cubic term in RegularizedPDE. Density cancellation gives Θε′≤(A₀/2+B)Θε+(A₀/2)L, so C=A₀/2+B controls Θε+L. The text distinguishes conditional ScalarCurveHypotheses from the actual geometric root, and avoids exchanging derivatives and ε limits. It expressly does not claim Θ local AC or an a.e. differential inequality.

6. **Energy proposition.** Checked against the exact LengthEstimates declarations: the supplied Ricci lower bound is over every p and every V with g(t)(V,V)=1 on [a,b]. The paper already says “every unit vector, at every point and time”, so this is a valid reading in the evolving metric. Weighted estimate accepts any real B; unweighted estimate correctly adds B≥0. The signs, exponential weights and L(b) terms agree with Lean.

7. **Compact tensor bounds.** Proposition matches the true `exists_uniformTensorBoundsOn`: jointly within smooth metric family and compact base, no Ricci PDE assumption. Actual multilinear metric norms are used. Its finite chart proof summary does not smuggle in globally continuous operator norms. The appendix's CompleteSpace observation is correct over finite-dimensional real models.

8. **Products.** The text correctly describes actual L² remodelled product geometry, metric-dependent fiber isometry, opposite-sign intrinsic curvature bridge, genuine Ricci trace and ∇Ric coefficient derivative. One-dimensional flatness and zero-field differentiation are correct; preserving the same B,K,D uses actual projection norms. Product Ricci flow is derived, not assumed. The statically supplied h has no Ricci-time dependence.

9. **Code mappings and provenance.** All 19 current `leanref` pairs were extracted and found in their exact module's compiled audit inventory. No reference points only to an imagined declaration. The caveats about reused infrastructure, fresh versus cached build, AI review versus human peer review, and finite extinction as downstream scope are appropriate.

## Optional clarifications (not mathematical blockers)

- Energy proposition: spell out “(g(t)(V,V)=1)” after “unit vector”, making the metric explicit without changing the hypothesis.
- Theorem with explicit ambient bounds: write “nonnegative B,K,D” within its own statement rather than rely on the preceding section's convention. Actual TensorBoundsAt includes nonnegativity.
- Product model paragraph: `\path{WithLp 2 (E * F)}` is not the literal Lean product type. Prefer “the L² type `WithLp 2` on (E\times F)” or another font-safe rendering rather than present `*` as executable Lean syntax.
- A mapping for the displayed connection-variation identity would improve navigation: `CurveControl.Geometry.RicciConnectionVariation.deriv_chartChristoffelBilin_lower_intrinsic`. Its omission currently causes no false claim.
- The compressed inequality hypotheses in theorem main use a shared ∀ℓ,i line over both initial inequalities; this is conventional and unambiguous in context. No rewrite is required.

## Bibliography check

Primary metadata checked against [Perelman's arXiv entry](https://arxiv.org/abs/math/0307245), [the correction to Section 19.2 entry](https://arxiv.org/abs/1512.00699), and [the book's title/copyright pages](https://www.claymath.org/library/monographs/cmim03.pdf): titles, authors, 17 July 2003 / 2 December 2015 submission dates, book year 2007 and Clay Mathematics Monographs volume 3 agree. The institutional publisher description is reasonable. Repository citations explicitly identify their pinned commits and do not claim a publication priority. No bibliography correction is required. Rendering of URLs by the chosen BibTeX style is a separate typesetting check.

## Acceptance scope after R1–R2

Accept the mathematical exposition after those two textual corrections and a final updated snapshot check. New StaticFactorApplication proof acceptance remains with its separately assigned reviewer; this review only establishes how its supplied statement changes the paper's claims. Rendering, bibliography layout, new environment audit coverage and release hashes remain the main agent's publication checks.

Presentation update (2026-09-10): the report now cites the exposition and correction by publication title and source identifier. The bibliographic metadata check above records the earlier review; this wording update does not change the mathematical source documents.
