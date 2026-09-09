<p align="center">
  <img src="docs/assets/ricci-curve-banner.en.svg" alt="Uniform curve estimates under Ricci flow — a Lean formalization" width="100%">
</p>

<p align="center">
  <strong>English</strong> · <a href="README.zh-CN.md">简体中文</a>
</p>

<p align="center">
  <strong>GPT-6 Astra · Juii-hang Leung</strong><br>
  Length and total-curvature estimates for the Perelman–Morgan–Tian finite extinction argument.
</p>

<p align="center">
  <a href="lean-toolchain"><img src="https://img.shields.io/badge/Lean-4.32.1-4066a5?style=flat-square" alt="Lean 4.32.1"></a>
  <a href="NOTICE"><img src="https://img.shields.io/badge/mathlib-pinned-657a58?style=flat-square" alt="Pinned mathlib dependency"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/License-Apache--2.0-526477?style=flat-square" alt="Apache 2.0 license"></a>
  <a href="https://github.com/LongWeihan/ricci-curve-estimates/actions/workflows/pages.yml"><img src="https://github.com/LongWeihan/ricci-curve-estimates/actions/workflows/pages.yml/badge.svg" alt="GitHub Pages deployment"></a>
  <a href="README.zh-CN.md"><img src="https://img.shields.io/badge/Readme-English%20%7C%20%E4%B8%AD%E6%96%87-237d85?style=flat-square" alt="Readme in English and Chinese"></a>
</p>

<p align="center">
  <a href="https://longweihan.github.io/ricci-curve-estimates/"><strong>Explore the website ↗</strong></a> ·
  <a href="https://longweihan.github.io/ricci-curve-estimates/blueprint.html">Proof blueprint</a> ·
  <a href="https://longweihan.github.io/ricci-curve-estimates/note.pdf">Technical report</a> ·
  <a href="docs/integration-guide.md">Integration guide</a>
</p>

---

This Lean 4 project formalizes uniform estimates for **existing smooth immersed closed curve-shortening flows** in a genuine Ricci-flow background. It derives the corrected curvature evolution, handles curvature zeros by regularization, integrates against moving arclength, and constructs constants uniform across static one-dimensional auxiliary factors.

## The estimate

For a compact base Ricci flow on a closed time interval $[a,b]$, the final product theorem selects $B,C\geq 0$ **before the auxiliary factor metrics, curve families, and initial bounds**. If every curve satisfies $L(a)\leq L_0$ and $\Theta(a)\leq\Theta_0$, then

$$
L(t)\leq L_0 e^{B(t-a)},\qquad
\Theta(t)\leq (\Theta_0+L_0)e^{C(t-a)},\qquad a\leq t\leq b.
$$

Here $L$ is length and $\Theta$ is total curvature, both measured using the evolving metric. The initial-length term is part of the corrected Morgan–Tian estimate.

The auxiliary factor is any supplied genuine one-dimensional smooth Riemannian manifold with a metric static in Ricci-flow time. The application constructs **$h_\lambda=\lambda^2h_0$ for every $\lambda>0$**, with no uniform positive lower bound on the scale, and derives bounds valid over the full time interval.

## Explore the project

| Start here | What you will find |
| :--- | :--- |
| [Interactive blueprint](https://longweihan.github.io/ricci-curve-estimates/blueprint.html) | 22 mathematical nodes linked to Lean declarations and their prerequisites |
| [Declaration browser](https://longweihan.github.io/ricci-curve-estimates/declarations.html) | Complete Lean types, assumptions, and source links |
| [Technical report · PDF](paper/curve-estimates.pdf) | Mathematical setting, corrected evolution, proof organization, and scope |
| [中文展示网页](https://longweihan.github.io/ricci-curve-estimates/zh/) | The same mathematical reference in Chinese |
| [Documentation](docs/index.md) | Integration, reproduction, contribution map, and semantic reviews |

## Use the Lean library

| Task | Entry module |
| :--- | :--- |
| Uniform estimates for arbitrary static factor-metric families | [UniformProductEstimates](CurveControl/Geometry/UniformProductEstimates.lean) |
| Construct scaled metrics and obtain full-interval bounds | [StaticFactorApplication](CurveControl/Examples/StaticFactorApplication.lean) |
| Curve estimates from explicit ambient tensor bounds | [CurveEstimates](CurveControl/Geometry/CurveEstimates.lean) |
| Length variation and accumulated curvature energy | [LengthEstimates](CurveControl/Geometry/LengthEstimates.lean) |

```lean
import CurveControl.Examples.StaticFactorApplication
```

See the [integration guide](docs/integration-guide.md) for exact theorem names and caller assumptions. To reproduce with existing matching dependency sources and the pinned Lean 4.32.1 toolchain:

```sh
python3 scripts/prepare_dependencies.py \
  --mathlib /path/to/mathlib4 \
  --geometry /path/to/Poincare-Conjecture
python3 scripts/verify.py
```

The [reproduction guide](docs/reproduction.md) also covers obtaining missing sources, dependency caches, and building the offline website. Toolchains and dependency caches are not bundled in this repository.

## Verification and scope

The bundled [release record](verification/release-check.json) reports a complete build and an audit of **796 project declarations**, with only `propext`, `Classical.choice`, and `Quot.sound` reachable. That evidence is tied to the source hashes and run recorded there. The [Lean workflow](https://github.com/LongWeihan/ricci-curve-estimates/actions/workflows/verify.yml) produces separate logs for hosted runs; the Pages badge above tracks website deployment.

The project proves the internal evolution, Kato, product-tensor splitting, integral differentiation, and comparison steps. Callers supply smooth flow existence, the factor manifold and starting metric, and common initial bounds. Concrete `AddCircle` atlases, ramp construction, continuation, and finite extinction itself remain outside the module. A standalone absolute-continuity/a.e. derivative interface for unregularized total curvature is also outside the current implementation.

Semantic reviews were performed by separate Astra AI agents; they are distinct from Lean checking and external human peer review. See [authors and tools](AUTHORS.md) and [release acceptance](docs/release-acceptance.md).

<details>
<summary><strong>Repository and publication notes</strong></summary>

- `CurveControl/` contains 44 mathematical modules; `CurveControl.lean` is the root import.
- `blueprint/` and `website-template/` provide the content and templates for the bilingual reference.
- `website/` contains the generated site; [GitHub Pages](docs/github-pages.md) automatically rebuilds and publishes it when its inputs change.
- `PACKAGE-MANIFEST.json` describes the original ZIP snapshot. Git history records the subsequent README and publication changes; historical verification records retain their original scope.

</details>

## Sources and citation

The development follows [Perelman’s finite extinction paper](https://arxiv.org/abs/math/0307245) and the [Morgan–Tian 2015 correction](https://arxiv.org/abs/1512.00699), and reuses pinned **mathlib** and **frenzymath DoCarmoLib/MorganTianLib** sources. The [contribution map](docs/contribution-map.md) distinguishes reused infrastructure from the formalization and integration supplied here.

Distributed under the [Apache License 2.0](LICENSE). See [NOTICE](NOTICE) for dependency provenance, [CITATION.bib](CITATION.bib) for the citation draft, and [CHANGELOG](CHANGELOG.md) for the project history. No new mathematical result, DOI, or formal publication is claimed.
