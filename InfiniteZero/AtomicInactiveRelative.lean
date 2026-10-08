import InfiniteZero.ActiveSaddleEnvelope
import InfiniteZero.AtomicInactiveCells
import InfiniteZero.RelativeNormalizationRatio
import InfiniteZero.InactiveCellNormSum

/-!
# The seven genuine inactive cells relative to the Gaussian saddle envelope

The radial normalization bound is applied to the exact state and coefficient
retained by the physical source estimates. No new state or coefficient is
chosen for the comparison. Both individual cells and the sum of their seven
norms are bounded, for the constructed state and the canonical state.
This compares proved inactive estimates with an explicit positive envelope;
it does not identify the asymptotic of either active cell.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

theorem exists_atomicGround_inactive_relative_of_radialData
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
          0 < p.activeSaddleEnvelope L coupling c Γ ∧
          let B := C * p.activeSaddleEnvelope L coupling c Γ *
            Real.exp (-15 * p.hopMargin * coupling)
          (∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
            ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ i j‖ ≤ B ∧
              ‖canonicalSourceCell p L coupling i j‖ ≤ B) ∧
          inactiveCellNormSum (sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ) ≤ B ∧
          inactiveCellNormSum (canonicalSourceCell p L coupling) ≤ B := by
  obtain ⟨K, hK, Ti, hTi, hinactive⟩ := exists_atomicGround_inactive_cells_of_radialData
    hInterior hp hRad hAcore hApot χ cert hL
  obtain ⟨D, hD, Tr, _hTr, hratio⟩ := exists_radialCore_normalizationRatio_bound_of_radialData
    hp.b_pos hp.r₀_pos hRad hAcore
  obtain ⟨Ta, _hTa, habsorb⟩ := exists_inactiveBound_le_activeSaddleEnvelope hp L hK hD
  let Cr := 4 * K * D / (p.ε ^ 2 * p.a ^ 2)
  have hCr : 0 < Cr := by
    have hε := hp.ε_pos
    have ha := hp.a_pos
    dsimp [Cr]
    positivity
  let threshold := max Ti (max Tr Ta)
  refine ⟨7 * Cr, by positivity, threshold, hTi.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hTs : Ti ≤ coupling ∧ Tr ≤ coupling ∧ Ta ≤ coupling := by
    simpa only [threshold, max_le_iff] using hc
  obtain ⟨hcTi, hcTr, hcTa⟩ := hTs
  obtain ⟨φ, ψ, hφ, hpos, hψ, c, hcRange, Γ, hΓ, htail, hE, hEr, hcells⟩ :=
    hinactive coupling hcTi
  have hr := (hratio coupling hcTr φ hφ hpos Γ htail).2.2 c hcRange.1
  obtain ⟨henv, hscale⟩ := habsorb coupling hcTa c hcRange.1 Γ hΓ hr
  let B₀ := Cr * p.activeSaddleEnvelope L coupling c Γ *
    Real.exp (-15 * p.hopMargin * coupling)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hpoint (i j : Fin 3) (hij₁ : (i, j) ≠ (1, 2)) (hij₂ : (i, j) ≠ (2, 1)) :
      ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ i j‖ ≤ B₀ ∧
        ‖canonicalSourceCell p L coupling i j‖ ≤ B₀ := by
    have hb := hcells i j hij₁ hij₂
    exact ⟨hb.1.trans hscale, hb.2.trans hscale⟩
  have hsum := inactiveCellNormSum_le_of_bound (fun i j h₁ h₂ => (hpoint i j h₁ h₂).1)
  have hsumCanonical := inactiveCellNormSum_le_of_bound
    (fun i j h₁ h₂ => (hpoint i j h₁ h₂).2)
  have hseven : 7 * B₀ = (7 * Cr) * p.activeSaddleEnvelope L coupling c Γ *
      Real.exp (-15 * p.hopMargin * coupling) := by dsimp [B₀]; ring
  have hle : B₀ ≤ (7 * Cr) * p.activeSaddleEnvelope L coupling c Γ *
      Real.exp (-15 * p.hopMargin * coupling) := by
    rw [← hseven]
    nlinarith
  refine ⟨φ, ψ, hφ, hpos, hψ, c, hcRange, Γ, hΓ, htail, hE, hEr, henv, ?_,
    hsum.trans_eq hseven, hsumCanonical.trans_eq hseven⟩
  intro i j h₁ h₂
  exact ⟨(hpoint i j h₁ h₂).1.trans hle, (hpoint i j h₁ h₂).2.trans hle⟩

end InfiniteZero.CuspParameters
