import InfiniteZero.Remaining
import InfiniteZero.RadialCoreFineForcingDerivatives

/-!
# The constructed potential's forcing derivatives, using only A002 and A004

The classical inputs concern the core realization and the radial core data.
Every cusp derivative, exact-action estimate, log-flat loss and L² bound is
proved in the imported analytic modules. No tunneling or source estimate
is assumed, and the main theorem is not used as an input.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

/-- Actual positive radial core states satisfy the common finite-order
forcing estimates for the explicit perturbation. The cutoff, constants and
threshold precede the coupling. Only A002 and A004 remain admitted. -/
theorem radialCore_fine_forcing_derivatives {p : CuspParameters}
    (hp : p.BasicConditions) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) (n : ℕ) :
    ∃ χ : CuspWeightCutoffs p, ∃ C > 0, ∃ N > 0,
      ∀ coupling : ℝ, N ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ ∧
      IsPositiveRadial φ ∧ ∃ Γ : ℝ, 0 < Γ ∧
        (∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel p.b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
        ∀ κ ∈ Icc (0 : ℝ) (1 / 16), ∀ j : ℕ, j ≤ n →
        ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
          MemLp (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) 2 volume ∧
          mass (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) ≤
            (C * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
              Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2 := by
  let χ := Classical.choice (exists_cuspWeightCutoffs hp)
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  exact ⟨χ, exists_positive_radialCore_fine_forcing_derivatives_mass_of_radialData
    hp hRad hAcore χ hβ₁ hβ₁β n⟩

end InfiniteZero.CuspParameters
