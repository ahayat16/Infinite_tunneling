import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicSourceProfiles

/-!
# Classical wrapper for the simultaneous physical source profiles

One pair of genuine atomic states supplies the incoming and scattered
sources on both cusp supports. Three independent logarithmic margins and
a fixed maximal jet order are chosen before all constants and couplings.
The admitted inputs are A002 and A004; the elliptic estimate is proved.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- The actual incoming and scattered cusp sources, with one common choice
of states and normalization, from the explicit potential conditions. -/
theorem atomicGround_source_profiles
    {p : CuspParameters} (hp : p.BasicConditions) {βin βglobal βlocal : ℝ}
    (hi : 0 < βin) (hiβ : βin < p.β)
    (hg : 0 < βglobal) (hgβ : βglobal < p.β)
    (hl : 0 < βlocal) (hlβ : βlocal < p.β) (n : ℕ) :
    ∃ κ₀ > 0, ∃ Cin > 0, ∃ Csc > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let A : ℝ := c * Γ *
            Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
            Real.exp (-βglobal * (Real.log coupling) ^ 2)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n →
            (∀ x ∈ tsupport p.cuspPlus,
              (coupling⁻¹) ^ j * ‖iteratedFDeriv ℝ j
                (atomicSource coupling⁻¹ p.atomicPerturbation (fun y => (c : ℂ) * φ y)) x‖ ≤
                Cin * c * Γ * coupling ^ (n + 4) *
                  logFlat βin p.tStar (p.normalCoordinate x) *
                  Real.exp (-coupling * (bridgeAction p.b
                    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
                    p.normalCoordinate x / 8))) ∧
            (∀ x ∈ tsupport p.cuspMinus,
              (coupling⁻¹) ^ j * ‖iteratedFDeriv ℝ j
                (atomicSource coupling⁻¹ p.atomicPerturbation (fun y => (c : ℂ) * φ y)) x‖ ≤
                Cin * c * Γ * coupling ^ (n + 4) *
                  logFlat βin p.tStar (p.normalCoordinate (reflection x)) *
                  Real.exp (-coupling * (bridgeAction p.b
                    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
                    p.normalCoordinate (reflection x) / 8))) ∧
            (∀ x ∈ tsupport p.cuspPlus,
              (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
                Csc * coupling ^ 6 * A * logFlat βlocal p.tStar (p.normalCoordinate x) *
                  Real.exp (-κ * coupling * p.normalCoordinate x)) ∧
            (∀ x ∈ tsupport p.cuspMinus,
              (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
                Csc * coupling ^ 6 * A *
                  logFlat βlocal p.tStar (p.normalCoordinate (reflection x)) *
                  Real.exp (-κ * coupling * p.normalCoordinate (reflection x))) := by
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
  exact exists_atomicGround_source_profiles_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ hi hiβ hg hgβ hl hlβ n

end InfiniteZero.CuspParameters
