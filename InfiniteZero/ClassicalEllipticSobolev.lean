import InfiniteZero.CoordinatePointEvaluation
import InfiniteZero.EllipticUniformInterior

/-!
# Point evaluation and interior Sobolev estimates

Point evaluation in `H²(B₁)` is proved in `CoordinatePointEvaluation.lean`
using a smooth cutoff, the fundamental theorem of calculus and
Cauchy–Schwarz. Interior elliptic regularity, including uniformity under
coefficient bounds, is proved in `EllipticUniformInterior.lean`. Applying
the point estimate to coordinate derivatives gives the higher-order
embedding used by the public elliptic estimate.

The point estimate is also a special case of J. K. Hunter, *Partial
Differential Equations*, Theorem 3.49(3), p.76, with dimension two,
`k = p = 2` and `m = 0`. The formal proof works directly with complex-valued
functions. See `docs/CLASSICAL_ELLIPTIC_INTERIOR.md` for the proof structure.
-/

namespace InfiniteZero

/-- A fixed constant controls `‖u 0‖` by the local `H²` norm on the unit
ball, for every smooth complex function. The estimate is proved from the
fundamental theorem of calculus and a fixed smooth cutoff. -/
theorem classical_h2_point_evaluation : HasH2PointEvaluation :=
  coordinateH2PointEvaluation

/-- The proved interior estimate and Sobolev embedding used by the
elliptic assembly. Neither estimate depends on an admission. -/
theorem classical_elliptic_sobolev_estimates :
    HasCoordinateInteriorSobolevEstimate ∧ HasCoordinateSobolevEmbedding :=
  ⟨coordinateInteriorSobolevEstimate,
    coordinateSobolevEmbedding_of_h2_pointEvaluation classical_h2_point_evaluation⟩

end InfiniteZero
