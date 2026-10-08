import InfiniteZero.LandauProperTimeEndpoints
import InfiniteZero.LandauRadialDerivatives

/-!
# Vanishing integral of the proper-time derivative

The exact radial differential identity and the integrability of both radial
derivatives imply integrability of the proper-time derivative. Its integral is
then zero by the fundamental theorem of calculus and the proved endpoint limits.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

/-- The time derivative is integrable; this is deduced from the actual
integrand and its radial derivatives, rather than assumed in the FTC step. -/
theorem integrableOn_deriv_landauIntegrand {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    IntegrableOn (deriv (landauIntegrand b h E r)) (Ioi 0) := by
  have hi := integrableOn_landauIntegrand hb hh hE hr
  have hd := integrableOn_landauIntegrandRadialDeriv hb hh hE hr
  have hdd := integrableOn_landauIntegrandRadialSecond hb hh hE hr
  have hint := (((hdd.add (hd.const_mul r⁻¹)).const_mul (-h ^ 2)).add
    (hi.const_mul (b ^ 2 * r ^ 2 / 4 + E))).const_mul (-h)⁻¹
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  change (-h)⁻¹ * (-h ^ 2 * (landauIntegrandRadialSecond b h E r τ +
    r⁻¹ * landauIntegrandRadialDeriv b h E r τ) +
    (b ^ 2 * r ^ 2 / 4 + E) * landauIntegrand b h E r τ) = _
  rw [landauIntegrand_radial_ode hb hh hr hτ E]
  simp [← mul_assoc, hh.ne']

/-- Integration of the exact proper-time derivative has no endpoint term. -/
theorem integral_Ioi_deriv_landauIntegrand_eq_zero {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    (∫ τ in Ioi (0 : ℝ), deriv (landauIntegrand b h E r) τ) = 0 := by
  have hderiv : ∀ τ ∈ Ioi (0 : ℝ),
      HasDerivAt (landauIntegrand b h E r) (deriv (landauIntegrand b h E r) τ) τ := by
    intro τ hτ
    exact (hasDerivAt_landauIntegrand_time hb hτ h E r).differentiableAt.hasDerivAt
  simpa [landauIntegrand] using integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousWithinAt_landauIntegrand_zero hb hh hr E) hderiv
    (integrableOn_deriv_landauIntegrand hb hh hE hr)
    (tendsto_landauIntegrand_atTop hb hh hE hr)

end InfiniteZero
