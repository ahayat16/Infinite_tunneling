import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicScatteredSourceJets

/-!
# Classical wrapper for the actual scattered cusp source

The two independently chosen logarithmic margins retain both the global
response decay and the local log-flat cusp profile. The same physical
states, normalization and exterior coefficient work for both closed cusp
supports and all prescribed jets. The classical inputs are A002, A004 and
A005; no source bound or tunneling asymptotic is admitted here.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- The true scattered cusp source and its two log-flat factors, from the
explicit potential conditions and the three documented classical inputs. -/
theorem atomicGround_scattered_source_jets
    {p : CuspParameters} (hp : p.BasicConditions)
    {βglobal βlocal : ℝ}
    (hg : 0 < βglobal) (hgβ : βglobal < p.β)
    (hl : 0 < βlocal) (hlβ : βlocal < p.β) (n : ℕ) :
    ∃ χ : CuspWeightCutoffs p,
    ∃ κ₀ > 0, ∃ Cη > 0, ∃ Csc > 0, ∃ threshold > 0,
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
          let A : ℝ := c * Γ *
            Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
            Real.exp (-βglobal * (Real.log coupling) ^ 2)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ ContDiff ℝ ∞ f ∧
          waveInner φ η = 0 ∧
          (∀ x : Plane,
            (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
              (magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) = f x) ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n →
            (∀ x ∈ closure p.cuspPacketInnerNeighborhood,
              Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j η x‖ ≤ Cη * coupling ^ 4 * A) ∧
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
  exact ⟨χ, exists_atomicGround_scattered_source_jets_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ hg hgβ hl hlβ n⟩

end InfiniteZero.CuspParameters
