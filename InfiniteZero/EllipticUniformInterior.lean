import InfiniteZero.EllipticLocalH2
import InfiniteZero.EllipticSobolevBootstrap

/-!
# Uniform interior regularity from the local energy estimates

The order-zero estimate is proved by cutoff energy identities and the
Hessian identity. The finite-order bootstrap supplies the dependence on
the indicated coefficient bounds. No Sobolev embedding or elliptic
regularity theorem is used to prove the gain of two derivatives here.
-/

noncomputable section
namespace InfiniteZero

/-- Interior regularity at every order, with constants fixed before all
coefficients satisfying their prescribed bounds. -/
theorem localCoordinateEllipticEstimate (n : ℕ) :
    HasLocalCoordinateEllipticEstimate n :=
  localCoordinateEllipticEstimate_of_zero hasLocalCoordinateEllipticEstimate_zero n

/-- The fixed-ball Sobolev estimate used by the public elliptic contract.
The coefficient uniformity is a proved conclusion. -/
theorem coordinateInteriorSobolevEstimate : HasCoordinateInteriorSobolevEstimate :=
  coordinateInteriorSobolevEstimate_of_local_zero hasLocalCoordinateEllipticEstimate_zero

end InfiniteZero
