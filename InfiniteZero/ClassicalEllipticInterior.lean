import InfiniteZero.EllipticInteriorContract

/-!
# A005: classical fixed-ball interior elliptic estimate

This documented classical admission contains only the universal estimate
for `-Δ + a · ∇ + q` on the Euclidean ball of radius two. All coefficient
bounds, changes of scale, weights and applications to the constructed
potential are proved separately with this contract as an explicit input.

References and the natural-language proof of the complex lower-order
variant are in `docs/CLASSICAL_ELLIPTIC_INTERIOR.md`: J. K. Hunter, PDE
notes, Theorems 4.27 (p.112), 4.28 (p.114) and 3.49 (p.76).
-/

namespace InfiniteZero

/-- A005, a universal classical interior estimate, independent of the
potential, semiclassical parameters, cusp weights and tunneling problem. -/
theorem classical_elliptic_interior_estimate : HasInteriorEllipticEstimate := by
  sorry

end InfiniteZero
