import InfiniteZero.RadialCoreProfileEstimates
import InfiniteZero.RadialWronskianComparison

/-! Comparison of the genuine core profile with its exterior Landau tail
throughout the punctured plane. The sign of the core potential determines
the Wronskian monotonicity; no Green-function normalization is assumed. -/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

theorem IsAtomicGroundState.radialCore_full_ode {b coupling : ℝ} {p : CuspParameters}
    {φ : Wavefunction} (hφ : IsAtomicGroundState b p.core coupling φ)
    (hpos : IsPositiveRadial φ) :
    IsRadialODESolutionOn (coreRadialODECoefficient b coupling p)
      (realRadialProfile φ) (deriv (realRadialProfile φ)) 0 := by
  have hf := realRadialProfile_contDiff hφ.1.1
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  constructor
  · intro r _
    exact (hf.differentiable (by simp) r).hasDerivAt
  · intro r hr
    change 0 < r at hr
    have hd := (hf'.differentiable (by simp) r).hasDerivAt
    have heq := hφ.1.radial_profile_equation hpos hr
    have hcoeff : b ^ 2 * coupling ^ 2 / 4 * r ^ 2 +
        coupling ^ 2 * p.core (r • coordinateVector 0) - atomicGroundEnergy b p.core coupling =
        coreRadialODECoefficient b coupling p r := by
      unfold coreRadialODECoefficient CuspParameters.coreRadialProfile
      ring
    rw [hcoeff] at heq
    convert hd using 1
    linarith only [heq]

/-- The kernel equation holds on the whole punctured positive half-line;
no regularity or integrability at the singular origin is asserted. -/
theorem isRadialODESolutionOn_landauKernel_zero {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) :
    IsRadialODESolutionOn (radialLandauCoefficient b h E)
      (landauKernel b h E) (deriv (landauKernel b h E)) 0 := by
  constructor
  · intro r hr
    change 0 < r at hr
    have hsol := isRadialODESolutionOn_landauKernel hb hh hE (half_pos hr)
    exact hsol.deriv r (by change r / 2 < r; linarith)
  · intro r hr
    change 0 < r at hr
    have hsol := isRadialODESolutionOn_landauKernel hb hh hE (half_pos hr)
    exact hsol.second r (by change r / 2 < r; linarith)

/-- The same Γ that represents the exterior tail bounds the actual profile
from above at every positive radius, including inside the core. -/
theorem IsAtomicGroundState.core_profile_le_landauKernel
    {b coupling E Γ : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) (hpos : IsPositiveRadial φ)
    (hb : 0 < b) (hc : 0 < coupling) (hr : 0 < p.r₀)
    (hE : E = -((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) (hEpos : 0 < E)
    (hΓ : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel b coupling⁻¹ E ‖x‖ : ℂ)) :
    ∀ r > 0, realRadialProfile φ r ≤ Γ * landauKernel b coupling⁻¹ E r := by
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hc
  intro r hrr
  apply le_mul_of_radialODE_coefficient_le (hφ.radialCore_full_ode hpos)
    (isRadialODESolutionOn_landauKernel_zero hb hh hEpos)
    (fun r _ => hpos.profile_pos r) (fun r hr' => landauKernel_pos hb hh hEpos hr')
  · intro r _
    have hcoeff : radialLandauCoefficient b coupling⁻¹ E r =
        coreRadialODECoefficient b coupling p r - coupling ^ 2 * p.coreRadialProfile r := by
      rw [hE]
      unfold radialLandauCoefficient coreRadialODECoefficient
      field_simp [hc.ne']
      ring
    rw [hcoeff]
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg coupling)
      (CuspParameters.core_range p (r • coordinateVector 0)).2
    change coupling ^ 2 * p.coreRadialProfile r ≤ 0 at hnonpos
    linarith only [hnonpos]
  · exact hr
  · intro r hr'
    have hrpos : 0 < r := hr.trans hr'
    have hnorm := norm_radial_axis hrpos.le
    have heq := hΓ (r • coordinateVector 0) (by simpa only [hnorm] using hr')
    have hreal := congrArg Complex.re heq
    simpa only [realRadialProfile, hnorm, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using hreal
  · exact hrr

end InfiniteZero
