import InfiniteZero.MagneticEllipticExpansion
import InfiniteZero.AffineScaleJets
import InfiniteZero.EllipticInteriorContract

/-!
# The magnetic equation on a fixed ball after affine rescaling

At `x = x₀ + h • y`, the relation `h = coupling⁻¹` cancels the
coupling in every first-order coefficient. The scalar coefficient uses
the already scaled energy `e = h² * E`. All identities concern the true
differential expressions and do not assume an elliptic estimate.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

/-- The first-order coefficient after rescaling; it remains imaginary. -/
def rescaledMagneticFirstOrder (b : ℝ) (x₀ : Plane) (h : ℝ) :
    Fin 2 → Wavefunction :=
  fun i y => Complex.I * (b : ℂ) * (perpCoordinate (affineScale x₀ h y) i : ℂ)

/-- The zeroth-order coefficient uses a real, already semiclassical energy. -/
def rescaledMagneticZerothOrder (b : ℝ) (V : Potential) (e : ℝ)
    (x₀ : Plane) (h : ℝ) : Wavefunction :=
  fun y => (((b / 2) ^ 2 * ‖affineScale x₀ h y‖ ^ 2 +
    V (affineScale x₀ h y) - e : ℝ) : ℂ)

/-- Exact operator rescaling, before imposing any equation or source.
Only nonzero coupling is required, and the potential is arbitrary. -/
theorem ellipticExpression_rescaledMagnetic
    (b coupling E : ℝ) (V : Potential) {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (hcoupling : coupling ≠ 0) (x₀ y : Plane) :
    ellipticExpression (rescaledMagneticFirstOrder b x₀ coupling⁻¹)
      (rescaledMagneticZerothOrder b V ((coupling⁻¹) ^ 2 * E) x₀ coupling⁻¹)
      (u ∘ affineScale x₀ coupling⁻¹) y =
      (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        (magneticHamiltonian b coupling V u (affineScale x₀ coupling⁻¹ y) -
          (E : ℂ) * u (affineScale x₀ coupling⁻¹ y)) := by
  have hc : (coupling : ℂ) ≠ 0 := by exact_mod_cast hcoupling
  rw [magneticHamiltonian_expansion b coupling V hu]
  simp only [ellipticExpression, Fin.sum_univ_two,
    partialDerivative_partialDerivative_affineScale hu,
    partialDerivative_affineScale (hu.differentiable (by simp)),
    rescaledMagneticFirstOrder, rescaledMagneticZerothOrder, Function.comp_apply]
  push_cast
  field_simp
  ring

/-- Pulling back the genuine semiclassical magnetic equation gives the
fixed-ball elliptic expression with the pulled-back source exactly. -/
theorem magneticEquation_affineScale
    (b coupling E : ℝ) (V : Potential) {u f : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (hcoupling : coupling ≠ 0)
    (heq : ∀ x : Plane, (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
      (magneticHamiltonian b coupling V u x - (E : ℂ) * u x) = f x)
    (x₀ y : Plane) :
    ellipticExpression (rescaledMagneticFirstOrder b x₀ coupling⁻¹)
      (rescaledMagneticZerothOrder b V ((coupling⁻¹) ^ 2 * E) x₀ coupling⁻¹)
      (u ∘ affineScale x₀ coupling⁻¹) y = f (affineScale x₀ coupling⁻¹ y) := by
  rw [ellipticExpression_rescaledMagnetic b coupling E V hu hcoupling]
  exact heq _

end InfiniteZero
