import InfiniteZero.SharpSaddleSize
import InfiniteZero.ActiveSaddleEnvelopeComparison

/-!
# Logarithmic reserves relative to the actual saddle envelope

An absolute logarithmic cost strictly greater than `2β` absorbs the inverse
square of the saddle size and every fixed polynomial loss. The reference
action and the physical normalization are preserved exactly. Thresholds are
uniform in the positive Schur coefficient and radial tail coefficient.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem exists_logarithmicBound_le_activeSaddleEnvelope
    {p : CuspParameters} (hp : p.BasicConditions) (L : ℝ)
    {q : ℝ} (hq : 2 * p.β < q) (N : ℕ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ c Γ : ℝ, 0 < c → 0 < Γ →
      0 < p.activeSaddleEnvelope L coupling c Γ ∧
      c ^ 2 * Γ ^ 2 * Real.exp (-coupling *
          (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)))) *
        coupling ^ N * Real.exp (-q * (Real.log coupling) ^ 2) ≤
        (p.ε ^ 2 * p.a ^ 2)⁻¹ * p.activeSaddleEnvelope L coupling c Γ *
          Real.exp (-((q - 2 * p.β) / 2) * (Real.log coupling) ^ 2) := by
  let δ := (q - 2 * p.β) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have htStar := hp.t₀_pos.trans hp.t₀_lt
  have hs := eventually_logFlatSaddleLeadingSize_pos (k := (2 : ℝ))
    hp.β_pos htStar (activeSaddleSlope_ne_zero hp L)
  have hb := eventually_inv_saddleLeadingSize_sq_polynomial_le_exp
    (k := (2 : ℝ)) hp.β_pos htStar (activeSaddleSlope_ne_zero hp L) hδ N
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (tendsto_inv_atTop_nhdsGT_zero.eventually (hs.and hb))
  refine ⟨max T 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hc c Γ hcp hΓ
  have hc1 : 1 ≤ coupling := (le_max_right _ _).trans hc
  have hcoupling : 0 < coupling := zero_lt_one.trans_le hc1
  obtain ⟨hsize, hbound⟩ := hT coupling ((le_max_left _ _).trans hc)
  simp only [inv_pow, inv_inv, one_div, inv_inv] at hbound
  let S := logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹
  let B := c ^ 2 * Γ ^ 2 * Real.exp (-coupling *
    (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsne : S ≠ 0 := hsize.ne'
  have hcancel : S ^ 2 * (S⁻¹ ^ 2 * coupling ^ N) = coupling ^ N := by
    field_simp
  have hpoly : coupling ^ N ≤
      S ^ 2 * Real.exp ((2 * p.β + δ) * (Real.log coupling) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hbound (sq_nonneg S)
    rw [← inv_pow S 2, hcancel] at hm
    exact hm
  have hcombine : Real.exp ((2 * p.β + δ) * (Real.log coupling) ^ 2) *
      Real.exp (-q * (Real.log coupling) ^ 2) =
      Real.exp (-δ * (Real.log coupling) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [δ]
    ring
  have hsqrt : 1 ≤ Real.sqrt coupling := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hc1
  have hpow : 1 ≤ coupling ^ 6 := one_le_pow₀ hc1
  have hprefactor : 1 ≤ coupling ^ 6 * Real.sqrt coupling :=
    one_le_mul_of_one_le_of_one_le hpow hsqrt
  refine ⟨activeSaddleEnvelope_pos hp L hcoupling hcp hΓ hsize, ?_⟩
  calc
    _ ≤ B * (S ^ 2 * Real.exp ((2 * p.β + δ) * (Real.log coupling) ^ 2)) *
        Real.exp (-q * (Real.log coupling) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hB)
        (Real.exp_pos _).le
    _ = B * S ^ 2 * Real.exp (-δ * (Real.log coupling) ^ 2) := by
      calc
        _ = B * S ^ 2 * (Real.exp ((2 * p.β + δ) * (Real.log coupling) ^ 2) *
            Real.exp (-q * (Real.log coupling) ^ 2)) := by ring
        _ = _ := by rw [hcombine]
    _ ≤ (B * (coupling ^ 6 * Real.sqrt coupling)) * S ^ 2 *
        Real.exp (-δ * (Real.log coupling) ^ 2) := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hprefactor hB
    _ = _ := by
      dsimp [B, S, δ, activeSaddleEnvelope]
      field_simp [hp.ε_pos.ne', hp.a_pos.ne']

theorem exists_logarithmicBound_le_activeSaddleTexEnvelope
    {p : CuspParameters} (hp : p.BasicConditions) (L : ℝ)
    {q : ℝ} (hq : 2 * p.β < q) (N : ℕ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ c Γ : ℝ, 0 < c → 0 < Γ →
      0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
      c ^ 2 * Γ ^ 2 * Real.exp (-coupling *
          (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)))) *
        coupling ^ N * Real.exp (-q * (Real.log coupling) ^ 2) ≤
        (2 / (p.ε ^ 2 * p.a ^ 2)) * p.activeSaddleTexEnvelope L coupling c Γ *
          Real.exp (-((q - 2 * p.β) / 2) * (Real.log coupling) ^ 2) := by
  obtain ⟨Tg, hTg, hgauss⟩ := exists_logarithmicBound_le_activeSaddleEnvelope hp L hq N
  obtain ⟨Tt, _hTt, htex⟩ := exists_activeSaddleEnvelope_comparison hp L
  refine ⟨max Tg Tt, hTg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc c Γ hcp hΓ
  obtain ⟨_, hbound⟩ := hgauss coupling ((le_max_left _ _).trans hc) c Γ hcp hΓ
  obtain ⟨hpos, _, hcompare⟩ := htex coupling ((le_max_right _ _).trans hc) c hcp Γ hΓ
  refine ⟨hpos, hbound.trans ?_⟩
  calc
    _ ≤ (p.ε ^ 2 * p.a ^ 2)⁻¹ * (2 * p.activeSaddleTexEnvelope L coupling c Γ) *
        Real.exp (-((q - 2 * p.β) / 2) * (Real.log coupling) ^ 2) := by
      gcongr
    _ = _ := by ring

end InfiniteZero.CuspParameters
