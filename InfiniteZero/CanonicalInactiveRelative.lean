import InfiniteZero.AtomicInactiveRelativeTex
import InfiniteZero.RadialCoreCoefficientUniqueness

/-!
# Universal normalization of the canonical inactive cells

The positive radial core state and its exact exterior coefficient are unique.
Consequently the relative estimate applies to any supplied such state and
coefficient. The normalization factor may be any real number at least one
half; it is not required to be selected by an overlap construction.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

/-- Changing the normalization in the literal saddle envelope costs at most
four when the original factor is in [0,1] and the new factor is at least 1/2. -/
theorem activeSaddleTexEnvelope_le_four_mul
    (p : CuspParameters) (L coupling Γ : ℝ) {c₀ c : ℝ}
    (hc₀ : c₀ ∈ Icc (0 : ℝ) 1) (hc : (1 / 2 : ℝ) ≤ c) :
    p.activeSaddleTexEnvelope L coupling c₀ Γ ≤
      4 * p.activeSaddleTexEnvelope L coupling c Γ := by
  have hs : c₀ ^ 2 ≤ 4 * c ^ 2 := by
    nlinarith [sq_nonneg (c - 1 / 2), mul_nonneg hc₀.1 (sub_nonneg.mpr hc₀.2)]
  let P := p.ε ^ 2 * p.a ^ 2 * Γ ^ 2 * coupling ^ 6 * Real.sqrt coupling *
    Real.exp (-coupling * (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)))) *
    (logFlatSaddleTexSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹) ^ 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  calc
    _ = c₀ ^ 2 * P := by unfold activeSaddleTexEnvelope P; ring
    _ ≤ (4 * c ^ 2) * P := mul_le_mul_of_nonneg_right hs hP
    _ = _ := by unfold activeSaddleTexEnvelope P; ring

/-- Uniform relative bounds for every supplied positive radial core ground
state, its own exact tail coefficient, and every normalization at least 1/2.
The canonical cells are independent of the unit phase of the full ground state. -/
theorem exists_canonical_inactive_relative_tex_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
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
  obtain ⟨C, hC, Ti, hTi, hi⟩ := exists_atomicGround_inactive_relative_tex_of_radialData
    hInterior hp hRad hAcore hApot χ cert hL
  refine ⟨4 * C, by positivity, max Ti hRad.threshold,
    hTi.trans_le (le_max_left _ _), ?_⟩
  intro coupling hcoup φ hφ hpos Γ _hΓ htail c hc
  obtain ⟨φ₀, ψ₀, hφ₀, hpos₀, _hψ₀, c₀, hc₀, Γ₀, _hΓ₀, htail₀,
    _hE, _hEr, hEnv₀, hcells, _hsum, hsumCanonical⟩ :=
      hi coupling ((le_max_left _ _).trans hcoup)
  have hΓeq := (hRad.positive_ground_coefficient_unique hp.r₀_pos (hAcore coupling)
    ((le_max_right _ _).trans hcoup) hφ₀ hpos₀ hφ hpos htail₀ htail).2
  subst Γ₀
  have hcompare := activeSaddleTexEnvelope_le_four_mul p L coupling Γ
    ⟨le_trans (by norm_num) hc₀.1, hc₀.2⟩ hc
  have hEnv : 0 < p.activeSaddleTexEnvelope L coupling c Γ := by linarith
  have hscale : C * p.activeSaddleTexEnvelope L coupling c₀ Γ *
      Real.exp (-15 * p.hopMargin * coupling) ≤
      (4 * C) * p.activeSaddleTexEnvelope L coupling c Γ *
        Real.exp (-15 * p.hopMargin * coupling) := by
    calc
      _ ≤ C * (4 * p.activeSaddleTexEnvelope L coupling c Γ) *
          Real.exp (-15 * p.hopMargin * coupling) := by gcongr
      _ = _ := by ring
  refine ⟨hEnv, ?_, hsumCanonical.trans hscale⟩
  intro i j h₁ h₂
  exact (hcells i j h₁ h₂).2.trans hscale

end InfiniteZero.CuspParameters
