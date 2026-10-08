import InfiniteZero.MagneticTestGraph

/-!
# The literal semiclassical magnetic differential expression

At nonzero `h`, multiplying the unit-field unscaled Hamiltonian at coupling
`h⁻¹` by `h²` gives `(-ih∇ - A)² + V`, with `A(x)=x⊥/2`.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

/-- The semiclassical covariant momentum `-ih∂ᵢ - (x⊥)ᵢ/2`. -/
def semiclassicalCovariantDerivative (h : ℝ) (i : Fin 2)
    (ψ : Wavefunction) : Wavefunction :=
  fun x => -Complex.I * (h : ℂ) * partialDerivative i ψ x -
    ((perpCoordinate x i / 2 : ℝ) : ℂ) * ψ x

/-- The literal unit-field expression `(-ih∇ - A)² + V`. -/
def semiclassicalMagneticHamiltonian (h : ℝ) (V : Potential)
    (ψ : Wavefunction) : Wavefunction :=
  fun x => (∑ i : Fin 2,
    semiclassicalCovariantDerivative h i (semiclassicalCovariantDerivative h i ψ) x) +
      (V x : ℂ) * ψ x

/-- A semiclassical momentum is `h` times the unscaled momentum at coupling `h⁻¹`. -/
theorem semiclassicalCovariantDerivative_eq_smul {h : ℝ} (hh : h ≠ 0)
    (i : Fin 2) (ψ : Wavefunction) :
    semiclassicalCovariantDerivative h i ψ = (h : ℂ) • covariantDerivative 1 h⁻¹ i ψ := by
  ext x
  simp only [semiclassicalCovariantDerivative, covariantDerivative,
    Pi.smul_apply, smul_eq_mul, one_mul]
  push_cast
  have hhc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp

/-- The semiclassical and unscaled differential expressions agree with the
exact factor `h²`; all differentiations are justified by smoothness. -/
theorem semiclassicalMagneticHamiltonian_eq_smul {h : ℝ} (hh : h ≠ 0)
    (V : Potential) {ψ : Wavefunction} (hψ : ContDiff ℝ ∞ ψ) :
    semiclassicalMagneticHamiltonian h V ψ =
      ((h ^ 2 : ℝ) : ℂ) • magneticHamiltonian 1 h⁻¹ V ψ := by
  have hD (i : Fin 2) : Differentiable ℝ (covariantDerivative 1 h⁻¹ i ψ) :=
    (contDiff_covariantDerivative 1 h⁻¹ i hψ).differentiable (by simp)
  ext x
  simp only [semiclassicalMagneticHamiltonian,
    semiclassicalCovariantDerivative_eq_smul hh, covariantDerivative_smul _ _ _ (hD _),
    Pi.smul_apply, smul_eq_mul, magneticHamiltonian, Fin.sum_univ_two]
  push_cast
  have hhc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp

end InfiniteZero
