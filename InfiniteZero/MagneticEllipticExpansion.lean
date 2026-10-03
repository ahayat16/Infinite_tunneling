import InfiniteZero.MagneticRadialReduction

/-!
# Exact elliptic expansion of the magnetic differential expression

The squared covariant derivatives are expanded using their proved local
product rule. The derivative of the magnetic coefficient in its own
coordinate direction vanishes. Summation gives the ordinary negative
Laplacian, the first-order magnetic term and the real scalar potential.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

/-- Pointwise elliptic expansion under precisely the differentiability
needed for the two coordinate derivatives. No regularity of `V` is used. -/
theorem magneticHamiltonian_expansion_local
    (b coupling : ℝ) (V : Potential) {u : Wavefunction} {x : Plane}
    (hu : DifferentiableAt ℝ u x)
    (hpartial : ∀ i : Fin 2, DifferentiableAt ℝ (partialDerivative i u) x) :
    magneticHamiltonian b coupling V u x =
      -(∑ i : Fin 2, partialDerivative i (partialDerivative i u) x) +
        (∑ i : Fin 2, (Complex.I * (b * coupling : ℂ) *
          (perpCoordinate x i : ℂ)) * partialDerivative i u x) +
        ((((b * coupling / 2) ^ 2 * ‖x‖ ^ 2 + coupling ^ 2 * V x : ℝ) : ℂ)) *
          u x := by
  have hnorm : (x 0 : ℂ) ^ 2 + (x 1 : ℂ) ^ 2 = (‖x‖ : ℂ) ^ 2 := by
    exact_mod_cast (show (x 0) ^ 2 + (x 1) ^ 2 = ‖x‖ ^ 2 by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two])
  simp only [magneticHamiltonian, Fin.sum_univ_two,
    covariantDerivative_squared_local b coupling 0 hu (hpartial 0),
    covariantDerivative_squared_local b coupling 1 hu (hpartial 1),
    perpCoordinate, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  push_cast
  rw [← hnorm]
  ring

/-- Global smoothness supplies the local hypotheses of the exact magnetic
expansion. This is an equality for the concrete Hamiltonian of the model. -/
theorem magneticHamiltonian_expansion
    (b coupling : ℝ) (V : Potential) {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (x : Plane) :
    magneticHamiltonian b coupling V u x =
      -(∑ i : Fin 2, partialDerivative i (partialDerivative i u) x) +
        (∑ i : Fin 2, (Complex.I * (b * coupling : ℂ) *
          (perpCoordinate x i : ℂ)) * partialDerivative i u x) +
        ((((b * coupling / 2) ^ 2 * ‖x‖ ^ 2 + coupling ^ 2 * V x : ℝ) : ℂ)) *
          u x :=
  magneticHamiltonian_expansion_local b coupling V
    ((hu.differentiable (by simp)).differentiableAt)
    (fun i => ((contDiff_partialDerivative i hu).differentiable (by simp)).differentiableAt)

end InfiniteZero
