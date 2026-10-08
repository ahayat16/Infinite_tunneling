import InfiniteZero.RadialCoreSpectralData
import InfiniteZero.RadialPlaneL2
import InfiniteZero.MagneticRadialReduction
import InfiniteZero.LandauExteriorUniqueness

/-! The exact exterior kernel formula for a genuine positive radial core
ground state. The differential equation and radial integrability are deduced
from the concrete eigenfunction, not postulated as spectral data. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem IsAtomicGroundState.radialCore_ode {b coupling : ℝ} {p : CuspParameters}
    {φ : Wavefunction} (hr : 0 < p.r₀) (hc : 0 < coupling)
    (hφ : IsAtomicGroundState b p.core coupling φ) (hpos : IsPositiveRadial φ) :
    IsRadialODESolutionOn
      (radialLandauCoefficient b coupling⁻¹
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)))
      (realRadialProfile φ) (deriv (realRadialProfile φ)) p.r₀ := by
  let f := realRadialProfile φ
  have hf : ContDiff ℝ ∞ f := realRadialProfile_contDiff hφ.1.1
  have hf' : ContDiff ℝ ∞ (_root_.deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hder (r : ℝ) : HasDerivAt f (_root_.deriv f r) r :=
    (hf.differentiable (by simp) r).hasDerivAt
  constructor
  · intro r _
    exact hder r
  · intro r hrr
    change p.r₀ < r at hrr
    have hrpos : 0 < r := hr.trans hrr
    have hnorm : ‖r • coordinateVector 0‖ = r := norm_radial_axis hrpos.le
    have hx : r • coordinateVector 0 ≠ 0 := by
      apply norm_pos_iff.mp
      rwa [hnorm]
    have hsecond := (hf'.differentiable (by simp) r).hasDerivAt
    have hformula := magneticHamiltonian_radial (fun s _ => hder s) hx
      (by simpa only [hnorm] using hsecond) b coupling p.core
    have hzero : p.core (r • coordinateVector 0) = 0 := by
      simp only [CuspParameters.core, hnorm, if_neg (not_lt.mpr hrr.le)]
    have heigen := hφ.1.2.2 (r • coordinateVector 0)
    have hradial : φ = fun x : Plane => (f ‖x‖ : ℂ) := hpos.eq_radial_function
    rw [hradial, hformula] at heigen
    simp only [hnorm, hzero, mul_zero, add_zero] at heigen
    have hreal := congrArg Complex.re heigen
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
      sub_zero] at hreal
    have hcoef : radialLandauCoefficient b coupling⁻¹
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) r =
        b ^ 2 * coupling ^ 2 / 4 * r ^ 2 - atomicGroundEnergy b p.core coupling := by
      unfold radialLandauCoefficient
      field_simp [hc.ne']
      ring
    have hode : _root_.deriv (_root_.deriv f) r =
        radialLandauCoefficient b coupling⁻¹
          (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) r * f r -
          r⁻¹ * _root_.deriv f r := by
      rw [hcoef]
      nlinarith only [hreal]
    rw [hode] at hsecond
    exact hsecond

/-- Exact exterior formula for any genuine positive radial ground state of
the core, at negative scaled ground energy. No bound on Γ is assumed. -/
theorem IsAtomicGroundState.exists_pos_radialCore_kernel
    {b coupling : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hb : 0 < b) (hr : 0 < p.r₀) (hc : 0 < coupling)
    (hφ : IsAtomicGroundState b p.core coupling φ) (hpos : IsPositiveRadial φ)
    (hE : (coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling < 0) :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel b coupling⁻¹
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ) := by
  have hfi := integrableOn_exterior_radial_sq_of_representation hr hφ.1.2.1 hpos.radial
  obtain ⟨Γ, hΓ, heq⟩ := exists_pos_eq_mul_landauKernel_of_radialODE
    hb (inv_pos.mpr hc) (neg_pos.mpr hE) hr
    (hφ.radialCore_ode hr hc hpos) hfi (fun r _ => hpos.profile_pos r)
  refine ⟨Γ, hΓ, fun x hx => ?_⟩
  rw [hpos.radial x, heq ‖x‖ hx]
  simp only [Complex.ofReal_mul]

/-- The actual core has a positive normalized ground state with the exact
exterior Landau tail at every sufficiently large coupling. The only input
is the classical radial one-well data; no exterior or tunneling assumption
is present. The threshold is chosen before the coupling. -/
theorem CuspParameters.exists_radialCore_kernel_of_radialData
    {p : CuspParameters} {b : ℝ} (hb : 0 < b) (hr : 0 < p.r₀)
    (hRad : RadialCoreSpectralData b p) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ ∧
        ∃ Γ : ℝ, 0 < Γ ∧ ∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ) := by
  refine ⟨max hRad.threshold (2 * hRad.energyBound),
    hRad.threshold_pos.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hT := (le_max_left hRad.threshold (2 * hRad.energyBound)).trans hc
  have hB := (le_max_right hRad.threshold (2 * hRad.energyBound)).trans hc
  obtain ⟨φ, hφ, hpos⟩ := hRad.positive_radial_ground coupling hT
  refine ⟨φ, hφ, hpos, ?_⟩
  exact hφ.exists_pos_radialCore_kernel hb hr (hRad.threshold_pos.trans_le hT) hpos
    (hRad.scaled_energy_neg hT hB)

end InfiniteZero
