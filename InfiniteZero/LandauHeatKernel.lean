import InfiniteZero.StandardLandauResolvent
import InfiniteZero.LandauResolventScaling

/-!
# Explicit magnetic Gaussian and its time integral

The field `B` is the physical magnetic field and the Planck constant is
one. The phase has the symmetric-gauge sign used throughout the project.
These are explicit functions; no semigroup identification is assumed.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

/-- Gaussian rate in the magnetic heat kernel. -/
def landauHeatRate (B t : ℝ) : ℝ :=
  B / 4 * (Real.cosh (B * t) / Real.sinh (B * t))

/-- Scalar prefactor of the two-dimensional magnetic heat kernel. -/
def landauHeatAmplitude (B t : ℝ) : ℝ :=
  B / (4 * Real.pi * Real.sinh (B * t))

/-- The explicit symmetric-gauge magnetic Gaussian. -/
def landauHeatKernel (B t : ℝ) (x y : Plane) : ℂ :=
  ((landauHeatAmplitude B t * Real.exp (-landauHeatRate B t * ‖x - y‖ ^ 2) : ℝ) : ℂ) *
    Complex.exp (-Complex.I * ((B / 2 * wedge x y : ℝ) : ℂ))

/-- Integration of the magnetic Gaussian against a pointwise source. -/
def landauHeatAction (B t : ℝ) (f : Wavefunction) : Wavefunction :=
  fun x => ∫ y : Plane, landauHeatKernel B t x y * f y

/-- The existing standard resolvent kernel applied to a pointwise source. -/
def standardLandauResolventAction (B ρ : ℝ) (f : Wavefunction) : Wavefunction :=
  fun x => ∫ y : Plane, freeLandauKernel B 1 ρ x y * f y

theorem landauHeatRate_pos {B t : ℝ} (hB : 0 < B) (ht : 0 < t) :
    0 < landauHeatRate B t := by
  unfold landauHeatRate
  exact mul_pos (by positivity)
    (div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.mpr (mul_pos hB ht)))

theorem landauHeatAmplitude_pos {B t : ℝ} (hB : 0 < B) (ht : 0 < t) :
    0 < landauHeatAmplitude B t := by
  unfold landauHeatAmplitude
  exact div_pos hB (mul_pos (by positivity)
    (Real.sinh_pos_iff.mpr (mul_pos hB ht)))

end InfiniteZero
