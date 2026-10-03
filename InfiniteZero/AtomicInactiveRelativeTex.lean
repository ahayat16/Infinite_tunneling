import InfiniteZero.AtomicInactiveRelative
import InfiniteZero.ActiveSaddleEnvelopeComparison

/-!
# The physical inactive cells relative to the manuscript's saddle envelope

Only a factor two is spent in comparing the scalar Hessian prefactors.
All states, coefficients and energies from the physical estimate are retained.
This does not assert an asymptotic for the active cells.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

theorem exists_atomicGround_inactive_relative_tex_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
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
  obtain ⟨C, hC, Ti, hTi, hi⟩ := exists_atomicGround_inactive_relative_of_radialData
    hInterior hp hRad hAcore hApot χ cert hL
  obtain ⟨Tt, _hTt, ht⟩ := exists_activeSaddleEnvelope_comparison hp L
  refine ⟨2 * C, by positivity, max Ti Tt, hTi.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  obtain ⟨φ, ψ, hφ, hpos, hψ, c, hcRange, Γ, hΓ, htail, hE, hEr,
    _hGpos, hcells, hsum, hsumCanonical⟩ := hi coupling ((le_max_left _ _).trans hc)
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hcRange.1
  obtain ⟨hTpos, _hlower, hupper⟩ := ht coupling ((le_max_right _ _).trans hc) c hcpos Γ hΓ
  have hscale : C * p.activeSaddleEnvelope L coupling c Γ *
      Real.exp (-15 * p.hopMargin * coupling) ≤
      (2 * C) * p.activeSaddleTexEnvelope L coupling c Γ *
        Real.exp (-15 * p.hopMargin * coupling) := by
    calc
      _ ≤ C * (2 * p.activeSaddleTexEnvelope L coupling c Γ) *
          Real.exp (-15 * p.hopMargin * coupling) := by gcongr
      _ = _ := by ring
  refine ⟨φ, ψ, hφ, hpos, hψ, c, hcRange, Γ, hΓ, htail, hE, hEr, hTpos, ?_,
    hsum.trans hscale, hsumCanonical.trans hscale⟩
  intro i j h₁ h₂
  exact ⟨(hcells i j h₁ h₂).1.trans hscale, (hcells i j h₁ h₂).2.trans hscale⟩

end InfiniteZero.CuspParameters
