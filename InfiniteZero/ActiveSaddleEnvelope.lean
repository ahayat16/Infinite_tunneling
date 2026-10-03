import InfiniteZero.GeometryActionSlopes
import InfiniteZero.HoppingChannels
import InfiniteZero.InactiveSupportGaps
import InfiniteZero.SaddleNormalizationIdentity

/-!
# A positive Gaussian saddle envelope for the physical active action

The slope uses the limiting energy one. The action retains the distinct
full and radial-core energies at the actual coupling. The exact factor
`coupling^6 * sqrt coupling` is coupling to the power thirteen halves.
The scalar size is the proved Gaussian normalization with `re w`, rather
than the manuscript's literal complex Hessian factor `1+w`. No active-cell
asymptotic is asserted by this definition or the comparison below.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

def activeSaddleSlope (p : CuspParameters) (L : ℝ) : ℂ :=
  (Geometry.activeActionSlope p.b 1 p.R L : ℂ) -
    Complex.I * (Geometry.phaseSlope p.b L : ℂ)

theorem activeSaddleSlope_re_pos {p : CuspParameters} (hp : p.BasicConditions) (L : ℝ) :
    0 < (p.activeSaddleSlope L).re :=
  Geometry.active_complex_slope_re_pos hp.b_pos.ne' (by norm_num) p.R L

theorem activeSaddleSlope_ne_zero {p : CuspParameters} (hp : p.BasicConditions) (L : ℝ) :
    p.activeSaddleSlope L ≠ 0 := by
  intro hz
  have hr := activeSaddleSlope_re_pos hp L
  simp only [hz, Complex.zero_re, lt_self_iff_false] at hr

def activeSaddleEnvelope (p : CuspParameters) (L coupling c Γ : ℝ) : ℝ :=
  p.ε ^ 2 * p.a ^ 2 * c ^ 2 * Γ ^ 2 * coupling ^ 6 * Real.sqrt coupling *
    Real.exp (-coupling * (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)))) *
    (logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹) ^ 2

theorem activeSaddleEnvelope_pos {p : CuspParameters} (hp : p.BasicConditions)
    (L : ℝ) {coupling c Γ : ℝ} (hCoupling : 0 < coupling) (hc : 0 < c) (hΓ : 0 < Γ)
    (hs : 0 < logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹) :
    0 < p.activeSaddleEnvelope L coupling c Γ := by
  unfold activeSaddleEnvelope
  have hε := hp.ε_pos
  have ha := hp.a_pos
  positivity

/-- The scalar saddle absorbs exactly the eighth polynomial power, with
all thresholds fixed before the coupling or physical normalization. -/
theorem exists_activeSaddleSize_regime {p : CuspParameters}
    (hp : p.BasicConditions) (L : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      1 ≤ coupling ∧
      0 < logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹ ∧
      (logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹)⁻¹ ^ 2 *
        coupling ^ 8 * Real.exp (-30 * p.hopMargin * coupling) ≤
          Real.exp (-15 * p.hopMargin * coupling) := by
  have htStar := hp.t₀_pos.trans hp.t₀_lt
  have hs := eventually_logFlatSaddleLeadingSize_pos (k := (2 : ℝ))
    hp.β_pos htStar (activeSaddleSlope_ne_zero hp L)
  have ha : 0 < 30 * p.hopMargin := mul_pos (by norm_num) (hopMargin_pos hp)
  have hb := eventually_inv_saddleLeadingSize_sq_polynomial_exp_le
    (k := (2 : ℝ)) hp.β_pos htStar (activeSaddleSlope_ne_zero hp L) ha 8
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (tendsto_inv_atTop_nhdsGT_zero.eventually (hs.and hb))
  refine ⟨max N 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hc
  obtain ⟨hsize, hbound⟩ := hN coupling ((le_max_left _ _).trans hc)
  refine ⟨(le_max_right _ _).trans hc, hsize, ?_⟩
  rw [show (30 * p.hopMargin) / 2 = 15 * p.hopMargin by ring] at hbound
  simpa only [inv_pow, inv_inv, div_inv_eq_mul, neg_mul] using hbound

/-- An absolute inactive-cell envelope becomes exponentially small relative
to the actual Gaussian saddle envelope. The normalization quotient is the
one later supplied for the very same radial state and exterior coefficient. -/
theorem exists_inactiveBound_le_activeSaddleEnvelope {p : CuspParameters}
    (hp : p.BasicConditions) (L : ℝ) {K D : ℝ} (hK : 0 < K) (hD : 0 < D) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ c : ℝ, (1 / 2 : ℝ) ≤ c → ∀ Γ : ℝ, 0 < Γ →
      (Γ ^ 2 + 1) / (c ^ 2 * Γ ^ 2) ≤ 4 * D * coupling ^ 4 →
      0 < p.activeSaddleEnvelope L coupling c Γ ∧
      K * (Γ ^ 2 + 1) * coupling ^ 10 *
        Real.exp (-coupling * (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
          (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) +
            31 * p.hopMargin)) ≤
        (4 * K * D / (p.ε ^ 2 * p.a ^ 2)) * p.activeSaddleEnvelope L coupling c Γ *
          Real.exp (-15 * p.hopMargin * coupling) := by
  obtain ⟨T, hT, hregime⟩ := exists_activeSaddleSize_regime hp L
  refine ⟨T, hT, ?_⟩
  intro coupling hcoupling c hc Γ hΓ hratio
  obtain ⟨hc1, hs, hbound⟩ := hregime coupling hcoupling
  have hcposCoupling : 0 < coupling := zero_lt_one.trans_le hc1
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  refine ⟨activeSaddleEnvelope_pos hp L hcposCoupling hcpos hΓ hs, ?_⟩
  let S := logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹
  let A := p.activeReferenceAction L (scaledAtomicEnergy p coupling)
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
  let P := 4 * K * D * c ^ 2 * Γ ^ 2 * coupling ^ 6 * Real.exp (-coupling * A)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hnorm : Γ ^ 2 + 1 ≤ (4 * D * coupling ^ 4) * (c ^ 2 * Γ ^ 2) :=
    (div_le_iff₀ (by positivity : 0 < c ^ 2 * Γ ^ 2)).mp hratio
  have hsne : S ≠ 0 := hs.ne'
  have hcancel : S ^ 2 * (S⁻¹ ^ 2 * coupling ^ 8 *
      Real.exp (-30 * p.hopMargin * coupling)) =
      coupling ^ 8 * Real.exp (-30 * p.hopMargin * coupling) := by
    field_simp
  have hscalar : coupling ^ 8 * Real.exp (-30 * p.hopMargin * coupling) ≤
      S ^ 2 * Real.exp (-15 * p.hopMargin * coupling) := by
    have hm := mul_le_mul_of_nonneg_left hbound (sq_nonneg S)
    rw [hcancel] at hm
    exact hm
  have hexp : Real.exp (-31 * p.hopMargin * coupling) ≤
      Real.exp (-30 * p.hopMargin * coupling) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_pos (hopMargin_pos hp) hcposCoupling]
  have hsplit : Real.exp (-coupling * (A + 31 * p.hopMargin)) =
      Real.exp (-coupling * A) * Real.exp (-31 * p.hopMargin * coupling) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsqrt : 1 ≤ Real.sqrt coupling := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hc1
  calc
    _ ≤ K * ((4 * D * coupling ^ 4) * (c ^ 2 * Γ ^ 2)) * coupling ^ 10 *
        Real.exp (-coupling * (A + 31 * p.hopMargin)) := by
      gcongr
    _ = P * (coupling ^ 8 * Real.exp (-31 * p.hopMargin * coupling)) := by
      rw [hsplit]
      dsimp [P]
      ring
    _ ≤ P * (coupling ^ 8 * Real.exp (-30 * p.hopMargin * coupling)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp (pow_nonneg hcposCoupling.le _)) hP
    _ ≤ P * (S ^ 2 * Real.exp (-15 * p.hopMargin * coupling)) :=
      mul_le_mul_of_nonneg_left hscalar hP
    _ ≤ (P * Real.sqrt coupling) * (S ^ 2 * Real.exp (-15 * p.hopMargin * coupling)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt hP
    _ = _ := by
      dsimp [P, S, A, activeSaddleEnvelope]
      field_simp [hp.ε_pos.ne', hp.a_pos.ne']

end InfiniteZero.CuspParameters
