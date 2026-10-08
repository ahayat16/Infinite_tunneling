import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.CanonicalInactiveRelative

/-!
# Classical wrapper for universal canonical inactive-cell estimates

The admitted inputs are A002 and A004; the elliptic estimate is proved.
The caller supplies the positive radial reference and its own exterior
coefficient; neither is reselected in the conclusion.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

theorem canonical_inactive_relative_tex {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ →
        IsPositiveRadial φ → ∀ Γ : ℝ, 0 < Γ →
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) →
        ∀ c : ℝ, (1 / 2 : ℝ) ≤ c →
          0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
          let B := C * p.activeSaddleTexEnvelope L coupling c Γ *
            Real.exp (-15 * p.hopMargin * coupling)
          (∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
            ‖canonicalSourceCell p L coupling i j‖ ≤ B) ∧
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
  exact exists_canonical_inactive_relative_tex_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ cert hL

end InfiniteZero.CuspParameters
