import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicActiveScatteredRelative

/-!
# Classical wrapper for removing the scattered active contribution

Only A002, A004 and A005 are supplied here. The source estimates, exact
pairing decomposition and comparison with the manuscript envelope are
proved. No active incoming asymptotic is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

theorem atomicGround_active_scattered_relative
    {p : CuspParameters} (hp : p.BasicConditions)
    {L β₀ : ℝ} (hL : p.R < 2 * L)
    (hβ₀ : 0 < β₀) (hβ₀β : β₀ < p.β) (hmargin : 2 * p.β < 3 * β₀) :
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
          let u : Wavefunction := fun x => (c : ℂ) * φ x
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let R := C * p.activeSaddleTexEnvelope L coupling c Γ *
            Real.exp (-((3 * β₀ - 2 * p.β) / 2) * (Real.log coupling) ^ 2)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
          ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ 1 2 -
            sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2‖ ≤ R ∧
          ‖canonicalSourceCell p L coupling 1 2 -
            sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2‖ ≤ R := by
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
  exact exists_atomicGround_active_scattered_relative_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ hL hβ₀ hβ₀β hmargin

/-- A fixed elementary margin removes all auxiliary logarithmic parameters. -/
theorem atomicGround_active_incoming_reduction
    {p : CuspParameters} (hp : p.BasicConditions)
    {L : ℝ} (hL : p.R < 2 * L) :
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
          let u : Wavefunction := fun x => (c : ℂ) * φ x
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let R := C * p.activeSaddleTexEnvelope L coupling c Γ *
            Real.exp (-(p.β / 8) * (Real.log coupling) ^ 2)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
          ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ 1 2 -
            sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2‖ ≤ R ∧
          ‖canonicalSourceCell p L coupling 1 2 -
            sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2‖ ≤ R := by
  have h := atomicGround_active_scattered_relative (β₀ := 3 * p.β / 4) hp hL
    (by linarith [hp.β_pos]) (by linarith [hp.β_pos]) (by linarith [hp.β_pos])
  simpa only [show (3 * (3 * p.β / 4) - 2 * p.β) / 2 = p.β / 8 by ring] using h

end InfiniteZero.CuspParameters
