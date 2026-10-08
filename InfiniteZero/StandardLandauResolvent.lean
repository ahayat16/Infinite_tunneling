import InfiniteZero.OperatorBridge
import InfiniteZero.LandauResolventBridge

/-!
# The free resolvent at Planck constant one

The standard Landau operator is `(-i∇ - B xᵖᵉʳᵖ/2)²` on physical `L²`.
`HasStandardLandauResolvent` states its integral-kernel formula at the
negative spectral parameter `-ρ`. It concerns vectors already in the
closed operator domain. Passing from a smooth square-integrable solution
to this domain and converting the semiclassical parameters are separate
proved steps.
-/

noncomputable section

open MeasureTheory

namespace InfiniteZero

/-- The classical integral-kernel identity for the closed free Landau
operator `H_B = (-i∇ - B xᵖᵉʳᵖ/2)²`, with Planck constant one.
For a domain vector `U` satisfying `(H_B + ρ)U = f`, where `f` is a smooth
compactly supported source, `U` is represented by the resolvent integral.

The kernel `freeLandauKernel B 1 ρ` is the magnetic phase
`exp(-i B (x ∧ y)/2)` times
`B/(4π) ∫₀^∞ exp(-ρt - B*coth(Bt)*|x-y|²/4)/sinh(Bt) dt`.
Its value on the diagonal is immaterial for this almost-everywhere
identity. Positivity of `B` and `ρ` is required by the theorem supplying
this contract. No smoothness or maximal-domain assertion about `U` is
part of this contract. -/
def HasStandardLandauResolvent (B ρ : ℝ) : Prop :=
  ∀ U : (magneticOperator B 1 0).domain, ∀ f : Wavefunction,
    IsTestFunction f →
    Represents (magneticOperator B 1 0 U + (ρ : ℂ) • (U : L2Space)) f →
    Represents (U : L2Space)
      (fun x => ∫ y : Plane, freeLandauKernel B 1 ρ x y * f y)

/-- With zero electric potential, the physical magnetic field is the
product `b * coupling`; absorbing the coupling into that field gives the
standard differential expression without changing coordinates. -/
theorem magneticHamiltonian_free_standard (b coupling : ℝ) (u : Wavefunction) :
    magneticHamiltonian b coupling 0 u =
      magneticHamiltonian (b * coupling) 1 0 u := by
  have hD (i : Fin 2) (v : Wavefunction) :
      covariantDerivative b coupling i v =
        covariantDerivative (b * coupling) 1 i v := by
    funext x
    simp only [covariantDerivative, mul_one]
  funext x
  simp only [magneticHamiltonian, hD, Pi.zero_apply, mul_zero,
    Complex.ofReal_zero, zero_mul, add_zero]

end InfiniteZero
