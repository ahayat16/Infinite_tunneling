import InfiniteZero.HoppingSourceIdentity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Converting the Landau kernel to Planck constant one

For coupling `λ > 0`, the free differential expression has magnetic field
`B = b λ`, and the positive resolvent parameter is `ρ = λ² E`. The proper-time
substitution `τ = λ t` identifies the kernel in these conventions with
`λ⁻² freeLandauKernel b λ⁻¹ E`. The identities include the value chosen by
the total Bochner integral on the diagonal; no integrability assertion at
the diagonal is needed for the change of variables.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- Exact rescaling of the proper-time integrand. -/
theorem landauIntegrand_coupling_rescale (b coupling E r t : ℝ) :
    landauIntegrand b coupling⁻¹ E r (coupling * t) =
      landauIntegrand (b * coupling) 1 (coupling ^ 2 * E) r t := by
  unfold landauIntegrand properTimePhase
  rw [show b * (coupling * t) = b * coupling * t by ring]
  congr 1
  congr 1
  simp only [div_inv_eq_mul, div_one]
  ring

/-- Positive linear substitution in the proper-time integral. This identity
also holds when the total Bochner integrals take their default value. -/
theorem integral_landauIntegrand_coupling_rescale (b E r : ℝ)
    {coupling : ℝ} (hc : 0 < coupling) :
    (∫ t in Ioi (0 : ℝ), landauIntegrand (b * coupling) 1 (coupling ^ 2 * E) r t) =
      coupling⁻¹ * ∫ τ in Ioi (0 : ℝ), landauIntegrand b coupling⁻¹ E r τ := by
  simp_rw [← landauIntegrand_coupling_rescale]
  simpa only [mul_zero, smul_eq_mul] using
    integral_comp_mul_left_Ioi (landauIntegrand b coupling⁻¹ E r) 0 hc

/-- The radial kernel in Planck-one units includes exactly the factor `λ⁻²`. -/
theorem landauKernel_coupling_rescale (b E r : ℝ)
    {coupling : ℝ} (hc : 0 < coupling) :
    (coupling⁻¹) ^ 2 * landauKernel b coupling⁻¹ E r =
      landauKernel (b * coupling) 1 (coupling ^ 2 * E) r := by
  unfold landauKernel
  rw [integral_landauIntegrand_coupling_rescale b E r hc]
  field_simp [hc.ne', Real.pi_ne_zero]

/-- The symmetric-gauge phase agrees under the same change of parameters. -/
theorem freeLandauKernel_coupling_rescale (b E : ℝ)
    {coupling : ℝ} (hc : 0 < coupling) (x y : Plane) :
    (((coupling⁻¹) ^ 2 : ℝ) : ℂ) * freeLandauKernel b coupling⁻¹ E x y =
      freeLandauKernel (b * coupling) 1 (coupling ^ 2 * E) x y := by
  have hp : b / (2 * coupling⁻¹) * wedge x y =
      (b * coupling) / (2 * 1) * wedge x y := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  unfold freeLandauKernel
  rw [hp, ← mul_assoc, ← Complex.ofReal_mul,
    landauKernel_coupling_rescale b E ‖x - y‖ hc]

/-- Moving the scale factor into the source integral gives the standard
Planck-one resolvent representation, for an arbitrary pointwise source. -/
theorem integral_freeLandauKernel_coupling_rescale (b E : ℝ)
    {coupling : ℝ} (hc : 0 < coupling) (x : Plane) (f : Wavefunction) :
    (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        (∫ y : Plane, freeLandauKernel b coupling⁻¹ E x y * f y) =
      ∫ y : Plane, freeLandauKernel (b * coupling) 1 (coupling ^ 2 * E) x y * f y := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [← mul_assoc, freeLandauKernel_coupling_rescale b E hc x y]

/-- The Planck-one radial kernel written in the conventional hyperbolic
proper-time form, with positive resolvent parameter `ρ = -z`. -/
theorem landauKernel_one_eq_properTime (B ρ r : ℝ) :
    landauKernel B 1 ρ r =
      B / (4 * Real.pi) * ∫ t in Ioi (0 : ℝ),
        (Real.sinh (B * t))⁻¹ *
          Real.exp (-(ρ * t + B * r ^ 2 / 4 * (Real.cosh (B * t) / Real.sinh (B * t)))) := by
  simp only [landauKernel, landauIntegrand, properTimePhase, one_pow, mul_one, div_one]

end InfiniteZero
