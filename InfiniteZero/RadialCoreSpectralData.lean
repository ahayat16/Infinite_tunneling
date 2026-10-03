import InfiniteZero.Construction
import InfiniteZero.RealRadialState

/-!
# Minimal radial spectral data

This structure is an input contract, not an assertion of existence. It only
concerns the radial core. In particular it contains no nonradial ground
state, source estimate, tunneling bound or noncompact form-integrability
assumption. The latter is no longer needed for localization.
The positive radial choice is the classical one-well conclusion of
Helffer--Kachmar, Theorem 1.1(2); it does not assert an exterior kernel formula.
-/

noncomputable section
namespace InfiniteZero

structure RadialCoreSpectralData (b : ℝ) (p : CuspParameters) where
  gap : ℝ
  gap_pos : 0 < gap
  energyBound : ℝ
  energyBound_pos : 0 < energyBound
  threshold : ℝ
  threshold_pos : 0 < threshold
  ground : ∀ coupling : ℝ, threshold ≤ coupling → ∃ φ : Wavefunction,
    IsAtomicGroundState b p.core coupling φ ∧
    let e := (coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling
    e ≤ -1 + energyBound / coupling ∧
    ∀ u : Wavefunction, IsTestFunction u →
      (gap * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
        magneticForm b coupling p.core u - coupling ^ 2 * e * mass u
  positive_radial_ground : ∀ coupling : ℝ, threshold ≤ coupling → ∃ φ : Wavefunction,
    IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ

/-- The sign required by the exterior Landau kernel follows from the
classical energy bound at an explicit enlarged threshold. -/
theorem RadialCoreSpectralData.scaled_energy_neg {b : ℝ} {p : CuspParameters}
    (hRad : RadialCoreSpectralData b p) {coupling : ℝ}
    (hT : hRad.threshold ≤ coupling) (hB : 2 * hRad.energyBound ≤ coupling) :
    (coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling < 0 := by
  have hc : 0 < coupling := hRad.threshold_pos.trans_le hT
  obtain ⟨φ, hφ, he, _⟩ := hRad.ground coupling hT
  have hquot : hRad.energyBound / coupling ≤ 1 / 2 :=
    (div_le_iff₀ hc).mpr (by linarith)
  linarith

end InfiniteZero
