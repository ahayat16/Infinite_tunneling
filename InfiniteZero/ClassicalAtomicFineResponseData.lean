import InfiniteZero.Remaining
import InfiniteZero.AtomicFineResponseDecomposition

/-!
# Classical wrapper for the complete fine response data

The cutoffs are chosen before every coupling and weight strength. The actual
core and full ground states, their common normalization and exterior radial
coefficient satisfy the exact scaled equation, the global response mass
bound and all finite-order local source bounds. Only the existing classical
realization A002 and radial spectral input A004 are instantiated here.
No free-resolvent admission or unfinished tunneling theorem is used.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- The genuine fine response and its full local PDE data, from the explicit
potential's elementary conditions and the two documented classical inputs.
The weight is chosen once before all constants and couplings. -/
theorem atomicGround_fine_response_data
    {p : CuspParameters} (hp : p.BasicConditions)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    (n : ℕ) :
    ∃ χ : CuspWeightCutoffs p,
    ∃ M > 0, ∃ _hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ Cresponse > 0, ∃ CdataL2 > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let f : Wavefunction := p.atomicScaledResponseSource coupling c φ
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ ContDiff ℝ ∞ f ∧
          waveInner φ η = 0 ∧
          (∀ κ ∈ Icc 0 κ₀,
            mass (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * η x) ≤
              (Cresponse * c * Γ * coupling ^ 3 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2) ∧
          (∀ x : Plane,
            (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
              (magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) = f x) ∧
          (∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n → ∀ v : Fin j → Plane,
            (∀ i, ‖v i‖ ≤ 1) →
            MemLp (p.cuspPacketNeighborhood.indicator
              (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) 2 volume ∧
            mass (p.cuspPacketNeighborhood.indicator
              (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) ≤
              (CdataL2 * c * Γ * coupling ^ 2 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2) ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ (ι : Type*) [Fintype ι] (orders : ι → ℕ),
            (∀ i, orders i ≤ n) → ∀ v : (i : ι) → Fin (orders i) → Plane,
            (∀ i j, ‖v i j‖ ≤ 1) →
            ∃ hF : ∀ i, MemLp (p.cuspPacketNeighborhood.indicator
                (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f (orders i) (v i))) 2 volume,
              (∑ i, ‖(hF i).toLp (p.cuspPacketNeighborhood.indicator
                (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f (orders i) (v i)))‖) ≤
                (Fintype.card ι : ℝ) * CdataL2 * c * Γ * coupling ^ 2 *
                  Real.exp (-coupling * bridgeAction p.b
                    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                  Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
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
  exact ⟨χ, exists_atomicGround_fine_response_decomposition_of_radialData
    hp hRad hAcore hApot χ hβ₁ hβ₁β n⟩

end InfiniteZero.CuspParameters
