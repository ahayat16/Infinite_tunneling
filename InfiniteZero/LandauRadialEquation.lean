import InfiniteZero.LandauProperTimeIntegral
import InfiniteZero.LandauRadialL2

/-! The actual positive proper-time kernel solves the radial exterior ODE.
All differentiations and endpoint integrations are justified by the preceding
modules. No Green-column identity or new classical admission is used. -/

noncomputable section
open Set MeasureTheory
namespace InfiniteZero

/-- Exact homogeneous radial Landau equation for the integral-defined kernel. -/
theorem landauKernel_radial_ode {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    -h ^ 2 * (deriv (deriv (landauKernel b h E)) r +
        r⁻¹ * deriv (landauKernel b h E) r) +
      (b ^ 2 * r ^ 2 / 4 + E) * landauKernel b h E r = 0 := by
  have hi := integrableOn_landauIntegrand hb hh hE hr
  have hd := integrableOn_landauIntegrandRadialDeriv hb hh hE hr
  have hdd := integrableOn_landauIntegrandRadialSecond hb hh hE hr
  have hint : (∫ τ in Ioi (0 : ℝ),
      -h ^ 2 * (landauIntegrandRadialSecond b h E r τ +
        r⁻¹ * landauIntegrandRadialDeriv b h E r τ) +
      (b ^ 2 * r ^ 2 / 4 + E) * landauIntegrand b h E r τ) = 0 := by
    calc
      _ = ∫ τ in Ioi (0 : ℝ), -h * deriv (landauIntegrand b h E r) τ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
        exact landauIntegrand_radial_ode hb hh hr hτ E
      _ = 0 := by rw [integral_const_mul, integral_Ioi_deriv_landauIntegrand_eq_zero hb hh hE hr,
        mul_zero]
  have hadd := integral_add ((hdd.add (hd.const_mul r⁻¹)).const_mul (-h ^ 2))
    (hi.const_mul (b ^ 2 * r ^ 2 / 4 + E))
  dsimp only [Pi.add_apply] at hadd
  rw [hadd, integral_const_mul,
    integral_add hdd (hd.const_mul r⁻¹), integral_const_mul, integral_const_mul] at hint
  rw [deriv_deriv_landauKernel hb hh hE hr, deriv_landauKernel hb hh hE hr]
  unfold landauKernel
  calc
    _ = (b / (4 * Real.pi * h ^ 2)) *
        (-h ^ 2 * ((∫ τ in Ioi (0 : ℝ), landauIntegrandRadialSecond b h E r τ) +
          r⁻¹ * ∫ τ in Ioi (0 : ℝ), landauIntegrandRadialDeriv b h E r τ) +
          (b ^ 2 * r ^ 2 / 4 + E) * ∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ) := by ring
    _ = 0 := by rw [hint, mul_zero]

end InfiniteZero
