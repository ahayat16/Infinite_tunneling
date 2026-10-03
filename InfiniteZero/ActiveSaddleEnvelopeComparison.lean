import InfiniteZero.ActiveSaddleEnvelope
import InfiniteZero.SaddleEnvelopeComparison

/-! Comparison with the literal complex-Hessian envelope of the manuscript. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

/-- The manuscript's positive envelope, using the same physical coefficients
and action as `activeSaddleEnvelope`, and the modulus of its complex Hessian. -/
def activeSaddleTexEnvelope (p : CuspParameters) (L coupling c Γ : ℝ) : ℝ :=
  p.ε ^ 2 * p.a ^ 2 * c ^ 2 * Γ ^ 2 * coupling ^ 6 * Real.sqrt coupling *
    Real.exp (-coupling * (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)))) *
    (logFlatSaddleTexSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹) ^ 2

/-- A common threshold works for every positive pair c,Γ: no physical
normalization is reselected when comparing the two scalar prefactors. -/
theorem exists_activeSaddleEnvelope_comparison {p : CuspParameters}
    (hp : p.BasicConditions) (L : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ c : ℝ, 0 < c → ∀ Γ : ℝ, 0 < Γ →
        0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
        p.activeSaddleTexEnvelope L coupling c Γ ≤ p.activeSaddleEnvelope L coupling c Γ ∧
        p.activeSaddleEnvelope L coupling c Γ ≤ 2 * p.activeSaddleTexEnvelope L coupling c Γ := by
  have hs := eventually_logFlatSaddleLeadingSize_sq_bounds (k := (2 : ℝ))
    hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_inv_atTop_nhdsGT_zero.eventually hs)
  refine ⟨max N 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hc c hcc Γ hΓ
  have hcpos : 0 < coupling := zero_lt_one.trans_le ((le_max_right _ _).trans hc)
  obtain ⟨hsize, hlower, hupper⟩ := hN coupling ((le_max_left _ _).trans hc)
  let P := p.ε ^ 2 * p.a ^ 2 * c ^ 2 * Γ ^ 2 * coupling ^ 6 * Real.sqrt coupling *
    Real.exp (-coupling * (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))))
  have hP : 0 < P := by
    have hε := hp.ε_pos
    have ha := hp.a_pos
    dsimp [P]
    positivity
  change 0 < P * _ ^ 2 ∧ P * _ ^ 2 ≤ P * _ ^ 2 ∧ P * _ ^ 2 ≤ 2 * (P * _ ^ 2)
  refine ⟨mul_pos hP (sq_pos_of_pos hsize), mul_le_mul_of_nonneg_left hlower hP.le, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hupper hP.le
  nlinarith only [hmul]

end InfiniteZero.CuspParameters
