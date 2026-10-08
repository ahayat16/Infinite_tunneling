import InfiniteZero.RadialCorePointwiseBound
import InfiniteZero.RadialCoreEnergyBounds
import InfiniteZero.LandauKernelUniform

/-!
# An exponential upper bound for the genuine radial exterior coefficient

At the fixed radius `2 * r₀`, unit mass and radial monotonicity bound the
profile from above. The uniform lower bound for the positive Landau kernel
then bounds every coefficient representing that same state's exterior tail.
The arbitrary positive action loss is fixed before all couplings and states.
Only the core realization and radial spectral data are needed to put the
actual scaled energy in the fixed interval `[1/2, 1]`.
-/

noncomputable section
open Set

namespace InfiniteZero

private theorem coefficient_le_of_exp_lower
    {c h A K B Γ : ℝ} (hc : 0 < c) (hh : 0 < h) (hB : 0 ≤ B)
    (hlower : (c / h ^ 2) * Real.exp (-A / h) ≤ K)
    (hvalue : Γ * K ≤ B) :
    Γ ≤ (B / c) * h ^ 2 * Real.exp (A / h) := by
  have hl : 0 < (c / h ^ 2) * Real.exp (-A / h) := by positivity
  have hK : 0 < K := hl.trans_le hlower
  calc
    Γ ≤ B / K := (le_div_iff₀ hK).mpr hvalue
    _ ≤ B / ((c / h ^ 2) * Real.exp (-A / h)) :=
      div_le_div_of_nonneg_left hB hl hlower
    _ = (B / c) * h ^ 2 * Real.exp (A / h) := by
      rw [neg_div, Real.exp_neg]
      field_simp

namespace CuspParameters

/-- The coefficient bound uses the exact tail of the supplied normalized
positive radial core state, at any positive kernel scale and any energy in
the fixed interval. In particular, it never replaces the supplied coefficient.
The scale need not yet be identified with the inverse coupling. -/
theorem exists_radialCore_coefficient_exp_upper {p : CuspParameters} {b η : ℝ}
    (hb : 0 < b) (hr₀ : 0 < p.r₀) (hη : 0 < η) :
    ∃ C > 0, ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ h > 0,
      ∀ coupling : ℝ, ∀ φ : Wavefunction,
        IsAtomicGroundState b p.core coupling φ → IsPositiveRadial φ →
        ∀ Γ : ℝ,
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel b h E ‖x‖ : ℂ)) →
          Γ ≤ C * h ^ 2 * Real.exp ((bridgeAction b E (2 * p.r₀) + η) / h) := by
  have hr : 0 < 2 * p.r₀ := by positivity
  obtain ⟨c, hc, hlower⟩ := exists_uniform_landauKernel_exp_lower
    hb (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hr (le_refl (2 * p.r₀)) hη
  let B : ℝ := 1 / (Real.sqrt Real.pi * (2 * p.r₀))
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B / c, div_pos hB hc, ?_⟩
  intro E hE h hh coupling φ hφ hpos Γ htail
  have hprofile : realRadialProfile φ (2 * p.r₀) ≤ B :=
    hφ.core_profile_le_inv_sqrt_pi_mul_radius hr₀ hpos hr
  have hvalue : Γ * landauKernel b h E (2 * p.r₀) ≤ B := by
    have ht := htail ((2 * p.r₀) • coordinateVector 0)
      (by rw [norm_radial_axis hr.le]; linarith)
    have hre := congrArg Complex.re ht
    simp only [norm_radial_axis hr.le, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at hre
    change realRadialProfile φ (2 * p.r₀) = _ at hre
    rw [← hre]
    exact hprofile
  exact coefficient_le_of_exp_lower hc hh hB.le
    (hlower E hE (2 * p.r₀) ⟨le_rfl, le_rfl⟩ h hh) hvalue

/-- For the actual core energy, one threshold suffices for every normalized
positive radial core ground state and every coefficient of its exact tail.
All constants precede the coupling, state and coefficient. -/
theorem exists_radialCore_coefficient_exp_upper_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ →
        IsPositiveRadial φ → ∀ Γ : ℝ,
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) →
          Γ ≤ C * (coupling⁻¹) ^ 2 * Real.exp (coupling *
            (bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
              (2 * p.r₀) + η)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_radialCore_coefficient_exp_upper hp.b_pos hp.r₀_pos hη
  obtain ⟨T, hT, henergy⟩ :=
    exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  refine ⟨C, hC, T, hT, ?_⟩
  intro coupling hc φ hφ hpos Γ htail
  have hcpos : 0 < coupling := hT.trans_le hc
  simpa only [div_eq_mul_inv, inv_inv, mul_comm coupling] using
    hbound _ (henergy coupling hc) coupling⁻¹ (inv_pos.mpr hcpos)
      coupling φ hφ hpos Γ htail

end CuspParameters
end InfiniteZero
