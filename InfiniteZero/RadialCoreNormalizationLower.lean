import InfiniteZero.RadialCoreKernelComparison
import InfiniteZero.LandauCoefficientBounds

/-!
# A polynomial lower bound for the genuine radial exterior coefficient

The central normalization and radial equation give a fixed positive lower
bound at radius h = 1/coupling. Wronskian comparison transfers it to Γ K(h).
The proved kernel bound then gives Γ ≥ c h² and Γ⁻¹ ≤ C h⁻². The constants
are fixed before the coupling, the positive radial state and its coefficient.
No harmonic profile limit or sharper h^(3/2) coefficient bound is asserted.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

/-- Uniform coefficient bounds for every normalized positive radial core
ground state and every coefficient representing its exact exterior tail. -/
theorem exists_radialCore_coefficient_bounds_of_radialData
    {p : CuspParameters} {b : ℝ} (hb : 0 < b) (hr : 0 < p.r₀)
    (hRad : RadialCoreSpectralData b p)
    (hAcore : ∀ coupling, IsMagneticRealization b coupling p.core) :
    ∃ c > 0, ∃ C > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ → IsPositiveRadial φ →
        ∀ Γ : ℝ,
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ)) →
          0 < Γ ∧ c * (coupling⁻¹) ^ 2 ≤ Γ ∧ Γ⁻¹ ≤ C * coupling ^ 2 := by
  obtain ⟨c₀, hc₀, Tinner, hTinner, hinner⟩ :=
    exists_core_profile_lower_of_radialData hr hRad hAcore
  refine ⟨c₀ * Real.pi / 2, by positivity, 2 / (c₀ * Real.pi), by positivity,
    max Tinner (max hRad.threshold (2 * hRad.energyBound)),
    hTinner.trans_le (le_max_left _ _), ?_⟩
  intro coupling hcoupling φ hφ hpos Γ hΓ
  have hTi : Tinner ≤ coupling := (le_max_left _ _).trans hcoupling
  have hT : hRad.threshold ≤ coupling :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hcoupling)
  have hB : 2 * hRad.energyBound ≤ coupling :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hcoupling)
  have hc : 0 < coupling := hRad.threshold_pos.trans_le hT
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hc
  obtain ⟨_, _, hupper, _⟩ := hRad.ground coupling hT
  have hquot : hRad.energyBound / coupling ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hc).mpr (by linarith)
  have hEhalf : (1 / 2 : ℝ) ≤
      -((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling) := by
    linarith only [hupper, hquot]
  have hEpos : 0 < -((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling) := by
    linarith only [hEhalf]
  have hvalue : c₀ ≤ Γ * landauKernel b coupling⁻¹
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) coupling⁻¹ :=
    (hinner coupling hTi φ hφ hpos coupling⁻¹ ⟨hh.le, le_rfl⟩).trans
      (hφ.core_profile_le_landauKernel hpos hb hc hr rfl hEpos hΓ coupling⁻¹ hh)
  refine ⟨landau_coefficient_pos_of_value_lower hb hh hEhalf hc₀ hvalue,
    landau_coefficient_lower_of_value_lower hb hh hEhalf hc₀ hvalue, ?_⟩
  simpa only [inv_inv] using
    landau_coefficient_inv_le_of_value_lower hb hh hEhalf hc₀ hvalue

/-- The same genuine positive radial state and exterior coefficient satisfy
the exact tail identity and both polynomial normalization bounds. -/
theorem exists_radialCore_kernel_coefficient_bounds_of_radialData
    {p : CuspParameters} {b : ℝ} (hb : 0 < b) (hr : 0 < p.r₀)
    (hRad : RadialCoreSpectralData b p)
    (hAcore : ∀ coupling, IsMagneticRealization b coupling p.core) :
    ∃ c > 0, ∃ C > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ ∧
        ∃ Γ : ℝ, 0 < Γ ∧ (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ)) ∧
          c * (coupling⁻¹) ^ 2 ≤ Γ ∧ Γ⁻¹ ≤ C * coupling ^ 2 := by
  obtain ⟨c, hc, C, hC, T₁, hT₁, hbounds⟩ :=
    exists_radialCore_coefficient_bounds_of_radialData hb hr hRad hAcore
  obtain ⟨T₂, hT₂, houter⟩ := exists_radialCore_kernel_of_radialData hb hr hRad
  refine ⟨c, hc, C, hC, max T₁ T₂, hT₁.trans_le (le_max_left _ _), ?_⟩
  intro coupling hcoupling
  obtain ⟨φ, hφ, hpos, Γ, hΓpos, hΓ⟩ :=
    houter coupling ((le_max_right _ _).trans hcoupling)
  obtain ⟨_, hlow, hinv⟩ :=
    hbounds coupling ((le_max_left _ _).trans hcoupling) φ hφ hpos Γ hΓ
  exact ⟨φ, hφ, hpos, Γ, hΓpos, hΓ, hlow, hinv⟩

end InfiniteZero.CuspParameters
