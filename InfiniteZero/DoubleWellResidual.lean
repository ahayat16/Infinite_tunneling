import InfiniteZero.MagneticCovariance

/-!
# Exact residuals of the translated atomic ground states

The reference energy is the energy of the same single-well potential `v`.
In particular, taking `v = p.potential` uses the full nonradial atom, not its
radial core. Magnetic covariance cancels the kinetic contribution exactly;
the residual consists only of the potential of the opposite well.
-/

noncomputable section

namespace InfiniteZero

/-- The left atomic state has precisely the right-well potential as its
double-well residual. No separation or asymptotic hypothesis is needed. -/
theorem IsAtomicGroundState.leftState_double_residual
    {b coupling : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (L : ℝ) (x : Plane) :
    doubleHamiltonian b v L coupling (leftState b L coupling φ) x -
      (atomicGroundEnergy b v coupling : ℂ) * leftState b L coupling φ x =
        ((coupling ^ 2 * v (-x + displacement L) : ℝ) : ℂ) *
          leftState b L coupling φ x := by
  have he := (hφ.leftState_eigenfunction L).1.2.2 x
  simp only [doubleHamiltonian, magneticHamiltonian, doubleWellPotential,
    mul_add, Complex.ofReal_add, add_mul] at he ⊢
  linear_combination he

/-- The right atomic state has precisely the left-well potential as its
double-well residual, with the same atomic energy as the left state. -/
theorem IsAtomicGroundState.rightState_double_residual
    {b coupling : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (L : ℝ) (x : Plane) :
    doubleHamiltonian b v L coupling (rightState b L coupling φ) x -
      (atomicGroundEnergy b v coupling : ℂ) * rightState b L coupling φ x =
        ((coupling ^ 2 * v (x + displacement L) : ℝ) : ℂ) *
          rightState b L coupling φ x := by
  have he := (hφ.rightState_eigenfunction L).1.2.2 x
  have harg : displacement L - x = -x + displacement L := by abel
  simp only [doubleHamiltonian, magneticHamiltonian, doubleWellPotential,
    harg, mul_add, Complex.ofReal_add, add_mul] at he ⊢
  linear_combination he

end InfiniteZero
