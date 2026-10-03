import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicInactiveRelativeTex

/-!
# Classical wrapper for relative inactive-cell bounds

Only A002, A004 and A005 are instantiated. The relative estimates use the
literal complex-Hessian saddle envelope. No active-cell asymptotic is
asserted: the comparison of scalar prefactors is proved separately.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

theorem atomicGround_inactive_relative_tex {p : CuspParameters} (hp : p.BasicConditions)
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
          0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
          let B := C * p.activeSaddleTexEnvelope L coupling c Γ *
            Real.exp (-15 * p.hopMargin * coupling)
          (∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
            ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ i j‖ ≤ B ∧
              ‖canonicalSourceCell p L coupling i j‖ ≤ B) ∧
          inactiveCellNormSum (sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ) ≤ B ∧
          inactiveCellNormSum (canonicalSourceCell p L coupling) ≤ B := by
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
  exact exists_atomicGround_inactive_relative_tex_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ cert hL

end InfiniteZero.CuspParameters
