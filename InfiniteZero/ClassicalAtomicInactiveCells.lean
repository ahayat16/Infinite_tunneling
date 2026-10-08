import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicInactiveCells

/-!
# Classical wrapper for the seven genuine inactive-cell bounds

The original source estimates and geometric action reserves are proved.
This wrapper uses the admitted inputs A002 and A004 and the proved elliptic
estimate. It keeps the radial exterior coefficient attached to the same
positive radial core state.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

theorem atomicGround_inactive_cells {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          scaledAtomicEnergy p coupling ∈ Icc (1 / 2 : ℝ) 1 ∧
          (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ∈
            Icc (1 / 2 : ℝ) 1 ∧
          ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
            let B := C * (Γ ^ 2 + 1) * coupling ^ 10 *
              Real.exp (-coupling * (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
                (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) +
                  31 * p.hopMargin))
            ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ i j‖ ≤ B ∧
              ‖canonicalSourceCell p L coupling i j‖ ≤ B := by
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
  exact exists_atomicGround_inactive_cells_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ cert hL

end InfiniteZero.CuspParameters
