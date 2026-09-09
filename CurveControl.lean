import CurveControl.Examples.StaticFactorApplication
import CurveControl.Analysis.CoupledComparison
import CurveControl.Analysis.CurvatureError
import CurveControl.Analysis.CurveEstimateAssembly
import CurveControl.Analysis.EnergyIntegral
import CurveControl.Analysis.IntegralEstimates
import CurveControl.Analysis.InteriorComparison
import CurveControl.Analysis.RegularizedIntegral
import CurveControl.Analysis.RegularizedNorm
import CurveControl.Analysis.RegularizedPDE
import CurveControl.Analysis.SmoothIntegral
import CurveControl.Analysis.WeightedIntegral
import CurveControl.Geometry.AmbientBounds
import CurveControl.Geometry.AmbientTensorExpansion
import CurveControl.Geometry.AmbientTensorRegularity
import CurveControl.Geometry.Basic
import CurveControl.Geometry.ChartBridge
import CurveControl.Geometry.ChartNormControl
import CurveControl.Geometry.CompactAmbientBounds
import CurveControl.Geometry.CurvatureEvolution
import CurveControl.Geometry.CurvatureGradient
import CurveControl.Geometry.CurveEstimates
import CurveControl.Geometry.CurveEvolution
import CurveControl.Geometry.CurveRegularity
import CurveControl.Geometry.EvolvingConnection
import CurveControl.Geometry.Flow
import CurveControl.Geometry.LengthEstimates
import CurveControl.Geometry.MovingMetric
import CurveControl.Geometry.OneDimensionalCurvature
import CurveControl.Geometry.ProductAmbientBounds
import CurveControl.Geometry.ProductChartCurvature
import CurveControl.Geometry.ProductConnection
import CurveControl.Geometry.ProductCovRicci
import CurveControl.Geometry.ProductFlow
import CurveControl.Geometry.ProductIntrinsicCurvature
import CurveControl.Geometry.ProductL2Connection
import CurveControl.Geometry.ProductMetric
import CurveControl.Geometry.ProductModel
import CurveControl.Geometry.ProductModelCoordinates
import CurveControl.Geometry.RicciConnectionVariation
import CurveControl.Geometry.RicciTraceProduct
import CurveControl.Geometry.SpatialCurve
import CurveControl.Geometry.SpeedEvolution
import CurveControl.Geometry.UniformProductEstimates

/-!
# Uniform curve control under Ricci flow

The root imports the full geometric and analytic proof chain, compact-ambient
tensor bounds, and the uniform static one-dimensional factor application.
Smooth immersed curve-shortening flow existence and the initial data remain
inputs. Internal evolution, regularization, integration, comparison, and the
auxiliary-factor independence of constants are proved in these modules.

See Geometry.UniformProductEstimates for the compact-base final theorem and
the positive-scale-indexed corollary. Audit.lean checks all imported project
declarations and their reachable axioms; semantic reviews are in docs/.
-/
