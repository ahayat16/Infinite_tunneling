import InfiniteZero.LandauHeatKernel

/-!
# The proper-time kernel as a Laplace transform

The free resolvent kernel is the time integral of the symmetric-gauge heat
kernel with weight `exp (-ρ t)`. This identity includes the diagonal value
assigned by the total Bochner integral.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

/-- The scalar proper-time integrand is the exponentially weighted heat
amplitude. The magnetic phase is independent of time. -/
theorem landauHeatLaplace_integrand (B ρ t : ℝ) (x y : Plane) :
    (Real.exp (-ρ * t) : ℂ) * landauHeatKernel B t x y =
      ((B / (4 * Real.pi) * ((Real.sinh (B * t))⁻¹ *
        Real.exp (-(ρ * t + B * ‖x - y‖ ^ 2 / 4 *
          (Real.cosh (B * t) / Real.sinh (B * t))))) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((B / 2 * wedge x y : ℝ) : ℂ)) := by
  unfold landauHeatKernel landauHeatAmplitude landauHeatRate
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [mul_left_comm (Real.exp _), ← Real.exp_add]
  rw [show -ρ * t + -(B / 4 * (Real.cosh (B * t) / Real.sinh (B * t))) *
      ‖x - y‖ ^ 2 = -(ρ * t + B * ‖x - y‖ ^ 2 / 4 *
        (Real.cosh (B * t) / Real.sinh (B * t))) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact Laplace representation of the Planck-one free Landau kernel. -/
theorem freeLandauKernel_eq_heatLaplace (B ρ : ℝ) (x y : Plane) :
    freeLandauKernel B 1 ρ x y =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-ρ * t) : ℂ) * landauHeatKernel B t x y := by
  simp_rw [landauHeatLaplace_integrand]
  rw [integral_mul_const, integral_complex_ofReal, integral_const_mul]
  simp only [freeLandauKernel, mul_one, landauKernel_one_eq_properTime]

end InfiniteZero
