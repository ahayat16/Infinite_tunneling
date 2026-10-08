import InfiniteZero.ClassicalEllipticSobolev
import InfiniteZero.EllipticSobolevAssembly

/-!
# Fixed-ball interior elliptic estimate

The directional-jet estimate for `-Δ + a · ∇ + q` combines the proved
uniform interior Sobolev estimate with the proved point estimate in `H²(B₁)`.
`EllipticSobolevAssembly.lean` supplies the source-norm conversion, tensor
norm comparison and combination of constants. Changes of scale, weights
and applications to the constructed potential are proved separately.

The proof structure and classical references are in `docs/CLASSICAL_ELLIPTIC_INTERIOR.md`.
-/

namespace InfiniteZero

/-- The public interior estimate used by the magnetic proofs, derived
from the proved interior Sobolev estimate and point evaluation in `H²`. -/
theorem classical_elliptic_interior_estimate : HasInteriorEllipticEstimate := by
  exact interiorEllipticEstimate_of_sobolev_estimates
    classical_elliptic_sobolev_estimates.1 classical_elliptic_sobolev_estimates.2

end InfiniteZero
