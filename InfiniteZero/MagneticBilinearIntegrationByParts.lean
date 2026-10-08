import InfiniteZero.MagneticInhomogeneousDomain

/-!
# Bilinear transposition of the magnetic Hamiltonian

Complex conjugation reverses the magnetic field. Consequently the
transpose of the differential expression in a bilinear integral is the
Hamiltonian with the opposite field. The source factor has compact
support; the other smooth factor may be a Gaussian kernel.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- Coordinate differentiation commutes with complex conjugation. -/
theorem partialDerivative_star (i : Fin 2) (u : Wavefunction) :
    partialDerivative i (star u) = star (partialDerivative i u) := by
  funext x
  change (fderiv ℝ (fun y => star (u y)) x) (coordinateVector i) =
    star ((fderiv ℝ u x) (coordinateVector i))
  simp only [fderiv_star,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]

/-- Complex conjugation reverses both the field and the sign of one
magnetic momentum. -/
theorem covariantDerivative_star (b coupling : ℝ) (i : Fin 2) (u : Wavefunction) :
    covariantDerivative b coupling i (star u) =
      -star (covariantDerivative (-b) coupling i u) := by
  funext x
  simp only [covariantDerivative, partialDerivative_star, Pi.star_apply, Pi.neg_apply,
    star_sub, star_mul, star_neg, Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal, neg_mul, neg_div, Complex.ofReal_neg]
  ring

/-- Conjugating the real-potential magnetic Hamiltonian reverses the field.
This identity is valid for the concrete differential expression. -/
theorem magneticHamiltonian_star (b coupling : ℝ) (V : Potential) (u : Wavefunction) :
    magneticHamiltonian b coupling V (star u) =
      star (magneticHamiltonian (-b) coupling V u) := by
  have hD (i : Fin 2) :
      covariantDerivative b coupling i (covariantDerivative b coupling i (star u)) =
        star (covariantDerivative (-b) coupling i (covariantDerivative (-b) coupling i u)) := by
    rw [covariantDerivative_star, covariantDerivative_neg, covariantDerivative_star, neg_neg]
  funext x
  simp only [magneticHamiltonian, hD, Pi.star_apply, star_add, star_sum, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- Bilinear integration by parts moves the magnetic Hamiltonian from a
compact smooth source to a smooth kernel while reversing the magnetic
field. No integrability assumption at spatial infinity is needed for the
kernel, because every integrand contains a compactly supported factor. -/
theorem integral_mul_magneticHamiltonian_eq
    (b coupling : ℝ) {V : Potential} (hV : Continuous V)
    {K φ : Wavefunction} (hK : ContDiff ℝ ∞ K) (hφ : IsTestFunction φ) :
    (∫ y : Plane, K y * magneticHamiltonian b coupling V φ y) =
      ∫ y : Plane, magneticHamiltonian (-b) coupling V K y * φ y := by
  have hstarφ : IsTestFunction (star φ) :=
    ⟨(starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hφ.1,
      hφ.2.comp_left (g := fun z : ℂ => star z) (by simp)⟩
  have h := waveInner_magneticHamiltonian_smooth_right (-b) coupling hV hstarφ hK
  rw [magneticHamiltonian_star, neg_neg] at h
  simpa only [waveInner, Pi.star_apply, star_star, mul_comm] using h.symm

end InfiniteZero
