import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicFineResponseJets

/-!
# Classical wrapper for fine pointwise atomic response jets

The cusp cutoffs precede all constants and couplings. For each sufficiently
large coupling the same positive radial core state, full ground state,
normalization and exterior coefficient work for every weight strength,
jet order up to the prescribed order, and point in the closed inner cusp
neighborhood. The classical inputs are exactly A002, A004 and A005.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- Fine weighted pointwise jets of the true atomic correction, under the
explicit potential conditions and the three documented classical inputs. -/
theorem atomicGround_fine_response_jets
    {p : CuspParameters} (hp : p.BasicConditions)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    (n : ℕ) :
    ∃ χ : CuspWeightCutoffs p,
    ∃ κ₀ > 0, ∃ C > 0, ∃ threshold > 0,
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
          (∀ x : Plane,
            (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
              (magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) = f x) ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n →
            ∀ x ∈ closure p.cuspPacketInnerNeighborhood,
              Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j η x‖ ≤
                C * c * Γ * coupling ^ 4 *
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
  exact ⟨χ, exists_atomicGround_fine_response_jets_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ hβ₁ hβ₁β n⟩

end InfiniteZero.CuspParameters
