import InfiniteZero.AtomicWeightedTail

/-! The exponential multiplier acts on the same physical representative.
Its Hilbert norm is the actual weighted wavefunction mass. -/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

theorem Represents.atomicExponentialWeightMul {u : L2Space} {φ : Wavefunction}
    (hu : Represents u φ) (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) :
    Represents (InfiniteZero.atomicExponentialWeightMul T hTc hT coupling κ u)
      (fun x => (Real.exp (κ * coupling * T x) : ℂ) * φ x) := by
  filter_upwards [coe_atomicExponentialWeightMul T hTc hT coupling κ u, hu]
    with x hw hx
  rw [hw, hx]

theorem Represents.mass_atomicExponentialWeightMul {u : L2Space} {φ : Wavefunction}
    (hu : Represents u φ) (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) :
    mass (fun x => (Real.exp (κ * coupling * T x) : ℂ) * φ x) =
      ‖InfiniteZero.atomicExponentialWeightMul T hTc hT coupling κ u‖ ^ 2 :=
  (hu.atomicExponentialWeightMul T hTc hT coupling κ).norm_sq_eq_mass.symm

end InfiniteZero
