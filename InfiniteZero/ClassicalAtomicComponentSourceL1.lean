import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicComponentSourceL1

/-!
# Classical wrapper for the three true component-source L¹ bounds

The admitted inputs are A002 and A004; the elliptic estimate is proved.
The core component retains its polynomial bound, while the sum of the two
cusp component norms has the exponential and log-flat decay. Every source
uses the same full ground state and the retained radial reference state.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem atomicGround_component_source_L1
    {p : CuspParameters} (hp : p.BasicConditions)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) :
    ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          (∀ i : Fin 3, Integrable (componentSource p coupling⁻¹ ψ i)) ∧
          ((∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 0 x‖) ≤
            coreSourceConstant p * coupling ^ 2) ∧
          ((∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 1 x‖) +
            (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 2 x‖) ≤
              C * Γ * coupling ^ 6 * Real.exp (-coupling * bridgeAction p.b
                (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) := by
  let χ := Classical.choice (exists_cuspWeightCutoffs hp)
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential := by
    intro coupling
    exact magnetic_realization p.b coupling p.potential
      (admissiblePotential hp).smooth (admissiblePotential hp).bounded
  exact exists_atomicGround_component_source_L1_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ hβ₁ hβ₁β

end InfiniteZero.CuspParameters
