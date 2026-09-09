# Uniform curve estimates under Ricci flow

**GPT-6 Astra · Juii-hang Leung**

A Lean module for the length and total-curvature estimates used in the Perelman–Morgan–Tian finite extinction argument. The proofs start from an existing smooth immersed closed curve-shortening flow in a genuine Ricci-flow background. They derive the corrected curvature evolution, handle curvature zeros, integrate against moving arclength, and construct constants uniform across static one-dimensional auxiliary factors.

[中文](README.zh-CN.md) · [Technical report (PDF)](paper/curve-estimates.pdf) · [Blueprint: English](website/index.html) · [中文](website/zh/index.html) · [Documentation](docs/index.md)

## Mathematical interface

Let `L` be curve length and `Θ` total curvature. For a compact base Ricci flow on `[a,b]`, the final product theorem chooses nonnegative constants `B,C` **before** all auxiliary factor metrics, curve families, and initial bounds. Given common initial bounds `L(a) ≤ L₀` and `Θ(a) ≤ Θ₀`, it proves, simultaneously for every curve, factor metric and `a ≤ t ≤ b`,

\[
L(t)\le L_0 e^{B(t-a)},\qquad
\Theta(t)\le(\Theta_0+L_0)e^{C(t-a)}.
\]

The initial-length term is essential to the corrected Morgan–Tian estimate. The product factor is any supplied genuine one-dimensional smooth Riemannian manifold with a metric static in Ricci-flow time. No lower bound on an auxiliary positive scale is required. The application module actually constructs `hλ = λ²h₀` from a supplied metric and derives full-interval bounds.

| Integration task | Entry point |
|---|---|
| Arbitrary static factor-metric families; positive scales | [UniformProductEstimates.lean](CurveControl/Geometry/UniformProductEstimates.lean) |
| Actual scaled metric and its application | [StaticFactorApplication.lean](CurveControl/Examples/StaticFactorApplication.lean) |
| Geometric length and total-curvature root with explicit ambient bounds | [CurveEstimates.lean](CurveControl/Geometry/CurveEstimates.lean) |
| Length variation and accumulated curvature energy | [LengthEstimates.lean](CurveControl/Geometry/LengthEstimates.lean) |
| Caller assumptions and exact theorem names | [Integration guide](docs/integration-guide.md) |

The implementation proves the internal PDE, Kato, tensor splitting, integral differentiation and comparison steps. The caller supplies flow existence, the genuine factor manifold and starting metric, and initial bounds. Concrete `AddCircle` atlases, ramp construction, continuation, and finite extinction itself are outside this module. The implementation compares regularized total curvature before taking a limit; it does not separately establish the blueprint's unregularized `Θ` absolute-continuity/a.e. interface.

## Review and reproduction

The [technical report](paper/curve-estimates.pdf) explains the mathematics and formalization choices; it is a technical review document for the code, not a claim of a new mathematical result. The [blueprint](website/index.html) connects proof stages to actual Lean declarations. The [contribution map](docs/contribution-map.md) distinguishes reused libraries from new proofs and integration.

Use the pinned Lean 4.32.1 toolchain and source dependencies described in [reproduction instructions](docs/reproduction.md). With existing matching source trees:

```sh
python3 scripts/prepare_dependencies.py --mathlib /path/to/mathlib4 --geometry /path/to/Poincare-Conjecture
python3 scripts/verify.py
```

The authoritative mechanical evidence is [verification/release-check.json](verification/release-check.json), including the actual run result and bound source hashes. Read it when checking coverage of this edition; historical review documents describe their own source snapshots. Semantic review is documented separately in [release acceptance](docs/release-acceptance.md) and the linked reviews. Independent semantic reviews were performed by Astra AI agents, not external human referees; see [AUTHORS.md](AUTHORS.md).

## Sources and attribution

This project reuses mathlib and the pinned frenzymath DoCarmoLib/MorganTianLib geometry libraries. Mathematical sources include [Perelman's finite extinction paper](https://arxiv.org/abs/math/0307245) and [Morgan–Tian's 2015 correction](https://arxiv.org/abs/1512.00699). It makes no priority or new-discovery claim.

See [LICENSE](LICENSE), [NOTICE](NOTICE), [CITATION.bib](CITATION.bib), and [CHANGELOG.md](CHANGELOG.md). No DOI or formal publication is claimed.
