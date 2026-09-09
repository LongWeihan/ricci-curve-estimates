# Genuine L2 product model and metric transport

2026-09-09, fixed mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6, Lean 4.32.1.

## Implemented in CurveControl/Geometry/ProductModel.lean

- `productL2Equiv : E × F ≃L[ℝ] WithLp 2 (E × F)` uses the inverse of `WithLp.prodContinuousLinearEquiv`.
- `productL2Model I J` applies this equivalence to `I.prod J`. Its chart-target type is **ModelProd H K**, not raw `H × K`: this tag is necessary for the canonical product ChartedSpace instance.
- `productL2_isManifold` proves the existing M×N atlas is smooth in this model.
- `productL2_boundaryless` proves no boundary when both original models are boundaryless, by transporting the full range through a surjective equivalence.
- `productModelDiffeomorph` is identity on points from the max-model product to the L2-model product. `productModelDiffeomorph_apply` is rfl.
- `productModelInverse_immersion` proves the inverse identity is a smooth immersion, using the actual diffeomorphism derivative continuous-linear equivalence to discharge differential injectivity.
- `productL2Metric I J g h` is the actual `DCProductMetric g h` pulled back by that inverse identity via `DCInducedMetric`. Smoothness, symmetry, positive definiteness and bounded unit balls are discharged by the upstream constructor, not supplied as placeholders.
- `productL2Metric_inner` gives exact equality to the original product metric on the mfderiv images of the new tangent vectors. No independent metric or curvature values are introduced.

The factors require their genuine InnerProductSpace structures; the L2 model gets the existing legitimate WithLp inner product. No InnerProductSpace instance on the max norm product is declared. The metric constructor needs finite-dimensional factors; the module does not require explicit CompleteSpace assumptions.

## Actual source APIs used

Mathlib paths below are relative to work/lean-deps/mathlib4-520045ab/Mathlib:

- Analysis/InnerProductSpace/ProdL2.lean:32 `WithLp.instProdInnerProductSpace`; :48 `prod_inner_apply` states sum of factor inner products.
- Analysis/Normed/Lp/ProdLp.lean:555 `WithLp.prodContinuousLinearEquiv` goes Lp→ordinary product; use `.symm` for model transport.
- Geometry/Manifold/Diffeomorph.lean:398 `ModelWithCorners.transContinuousLinearEquiv`; :455 `ContinuousLinearEquiv.instIsManifoldtransContinuousLinearEquiv`; :469 `toTransContinuousLinearEquiv`.
- Geometry/Manifold/LocalDiffeomorph.lean:428 `Diffeomorph.mfderivToContinuousLinearEquiv`; :433 identifies its underlying continuous linear map with actual mfderiv.
- Geometry/Manifold/ChartedSpace.lean:400 `ModelProd`, :440 `prodChartedSpace`.

Existing frenzy DoCarmoLib:

- Riemannian/Manifold/DoCarmoCh1.lean:346 `DCSmoothImmersion`, :352 `DCInducedForm`, :474 `DCInducedMetric`, :544 `DCProductMetric`.
- The pullback is along a proven smooth immersion; no target-assuming `IsPullbackMetricSmooth` field is introduced by our module.

## What is not yet proved here

1. An explicit formula identifying the inverse identity mfderiv with the pointwise L2→max coordinate conversion. The current theorem retains the genuine mfderiv, so it is already a legitimate metric construction, but coordinate interoperability can be made easier.
2. Naturality of canonical LC, Rm, Ric and covRic under this identity diffeomorphism, or direct chart formulas for the transported L2 metric. The product Christoffel splitting agent must connect its max-model chart results through this change. The metric construction alone proves no product curvature identity.
3. Circle atlas, circle metric construction, λ-independent product bounds, curve-estimate root integration remain outside this module. A one-dimensional Riemannian factor, once constructed, can use OneDimensionalCurvature independently.

## Mechanical evidence

Final source SHA256: d6b38166051d3dd77b9a5a0ae05a33d1aedf0e4ccca39ba9649bc53059d05328.
`audit_proofs.py` compiled final source and printed axioms for all 7 named def/theorem declarations: exit 0, 7/7 found, no extra axioms. Evidence in outputs/poincare-curve-control/verification/CurveControl-Geometry-ProductModel.{json,log}. Instance declarations are separately printed in work/lean-start/product-model-instances.log because the generic audit scanner does not enumerate instances. No source changes to another agent's module, configurations, or dashboard.
