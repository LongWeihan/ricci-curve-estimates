# Documentation

## Start with the mathematical interface

- [Technical report (PDF)](../paper/curve-estimates.pdf): theorem statements, proof organization, conventions and limitations; [LaTeX source](../paper/curve-estimates.tex).
- [Interactive blueprint](../website/index.html): proof dependencies linked to real Lean declarations.
- [Integration guide](integration-guide.md): inputs, exact entry points and the concrete scaled-factor application.
- [Contribution map](contribution-map.md): reused geometry and analysis, adaptations, and new integration.
- [Reproduction](reproduction.md): pinned sources, preparation, build and audit commands.

## Evidence and semantic review

[release-check.json](../verification/release-check.json) is the machine-readable record for its actual verification run and source hashes. [Release acceptance](release-acceptance.md) links semantic reviews and explains the evidence boundary. Earlier reviews retain their historical context; use the final review and matching source hashes to assess resolved issues.

- [Geometric input definitions](geometry-definition-review.md)
- [Spatial connection formulation](spatial-connection-route.md)
- [Actual curvature root and curve estimates](curvature-root-semantic-review.md)
- [Integral regularity](regularity-and-integral-semantic-review.md)
- [Estimate assembly](estimate-assembly-semantic-review.md)
- [Compact ambient bounds](ambient-bounds-foundations-review.md)
- [Final product uniformity](final-uniformity-semantic-review.md)
- [Reproduction tooling review](reproducibility-review.md)
- [Scaled-factor application review](scaled-factor-semantic-review.md)
- [Report and blueprint semantic review](publication-semantic-review.md)
- [Publication tooling review](publication-tooling-review.md)
- [Current bilingual exposition review](minimal-exposition-review.md)
- [Independent blueprint review](blueprint-independent-review.md)
- [Chinese blueprint review](chinese-blueprint-review.md)
- [Bilingual website tooling review](bilingual-tooling-review.md)
- [Isolated project reproduction](isolated-reproduction.md)

Review methods are recorded in [AUTHORS](../AUTHORS.md). See also [NOTICE](../NOTICE), [citation](../CITATION.bib), and the [changelog](../CHANGELOG.md).
