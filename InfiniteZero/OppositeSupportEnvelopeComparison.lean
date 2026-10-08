import InfiniteZero.ActiveSaddleEnvelopeComparison
import InfiniteZero.AtomicGroundEnergyBounds

/-!
# A strict bridge-action reserve relative to the active saddle envelope

The physical core and full energies are kept distinct. The same coefficients
`c` and `Γ` occur on both sides, and the threshold precedes these coefficients.
The only scalar asymptotic used is the proved saddle-size absorption estimate.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

/-- The fine squared opposite-support majorant, with its actual two energies. -/
def oppositeSupportFineBound (p : CuspParameters) (L K coupling c Γ : ℝ) : ℝ :=
  K * c ^ 2 * Γ ^ 2 * coupling ^ 15 *
    Real.exp (-2 * coupling *
      (bridgeAction p.b (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
        bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)))

theorem exists_oppositeSupportBound_le_activeSaddleTexEnvelope
    {p : CuspParameters} (hp : p.BasicConditions) {L K : ℝ}
    (hL : p.R < L) (hK : 0 ≤ K) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (1 / 2 : ℝ) ≤ scaledAtomicEnergy p coupling →
      ∀ c : ℝ, 0 < c → ∀ Γ : ℝ, 0 < Γ →
        0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
        p.oppositeSupportFineBound L K coupling c Γ ≤
          (2 * K / (p.ε ^ 2 * p.a ^ 2)) *
            p.activeSaddleTexEnvelope L coupling c Γ *
              Real.exp (-(2 * L - p.R) * coupling / 4) := by
  have hR : 0 < p.R := by linarith [hp.radius_large, hp.r₀_pos]
  have hd : 0 < 2 * L - p.R := by linarith
  let a := (2 * L - p.R) / 2
  have ha : 0 < a := half_pos hd
  have hs := eventually_logFlatSaddleLeadingSize_pos (k := (2 : ℝ))
    hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L)
  have hb := eventually_inv_saddleLeadingSize_sq_polynomial_exp_le
    (k := (2 : ℝ)) hp.β_pos (hp.t₀_pos.trans hp.t₀_lt)
    (activeSaddleSlope_ne_zero hp L) ha 9
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (tendsto_inv_atTop_nhdsGT_zero.eventually (hs.and hb))
  obtain ⟨Te, _hTe, he⟩ := exists_activeSaddleEnvelope_comparison hp L
  refine ⟨max (max N Te) 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hc hE c hcc Γ hΓ
  have hc1 : 1 ≤ coupling := (le_max_right _ _).trans hc
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  have hcN : N ≤ coupling := (le_max_left N Te).trans ((le_max_left _ _).trans hc)
  have hcTe : Te ≤ coupling := (le_max_right N Te).trans ((le_max_left _ _).trans hc)
  obtain ⟨hsize, hbound⟩ := hN coupling hcN
  obtain ⟨henvpos, _henvlo, henvup⟩ := he coupling hcTe c hcc Γ hΓ
  refine ⟨henvpos, ?_⟩
  let S := logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹
  let G := bridgeAction p.b
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R
  let J := bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)
  let A := p.activeReferenceAction L (scaledAtomicEnergy p coupling)
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
  let P := K * c ^ 2 * Γ ^ 2 * coupling ^ 6 * Real.exp (-coupling * A)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hEpos : 0 < scaledAtomicEnergy p coupling := lt_of_lt_of_le (by norm_num) hE
  have hsqrtE : (1 / 2 : ℝ) ≤ Real.sqrt (scaledAtomicEnergy p coupling) := by
    have hsq := Real.sq_sqrt hEpos.le
    have hn := Real.sqrt_nonneg (scaledAtomicEnergy p coupling)
    nlinarith
  have hJ : a ≤ J := by
    have hlow := bridgeAction_ge_sqrt_energy_mul hp.b_pos.ne' hEpos
      (show 0 ≤ Geometry.activeDistance p.R L from hd.le)
    have hm := mul_le_mul_of_nonneg_right hsqrtE hd.le
    dsimp [a, J, Geometry.activeDistance] at *
    linarith
  have hsne : S ≠ 0 := hsize.ne'
  have hscalar0 : S⁻¹ ^ 2 * coupling ^ 9 * Real.exp (-a * coupling) ≤
      Real.exp (-(a / 2) * coupling) := by
    simpa only [S, inv_pow, inv_inv, div_inv_eq_mul] using hbound
  have hscalar : coupling ^ 9 * Real.exp (-a * coupling) ≤
      S ^ 2 * Real.exp (-(a / 2) * coupling) := by
    have hm := mul_le_mul_of_nonneg_left hscalar0 (sq_nonneg S)
    have hcancel : S ^ 2 * (S⁻¹ ^ 2 * coupling ^ 9 * Real.exp (-a * coupling)) =
        coupling ^ 9 * Real.exp (-a * coupling) := by field_simp
    rwa [hcancel] at hm
  have hsplit : Real.exp (-2 * coupling * (G + J)) =
      Real.exp (-coupling * A) * Real.exp (-coupling * J) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [A, G, J, activeReferenceAction]
    ring
  have hexp : Real.exp (-coupling * J) ≤ Real.exp (-a * coupling) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsqrt : 1 ≤ Real.sqrt coupling := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hc1
  have hGaussian : p.oppositeSupportFineBound L K coupling c Γ ≤
      (K / (p.ε ^ 2 * p.a ^ 2)) * p.activeSaddleEnvelope L coupling c Γ *
        Real.exp (-(2 * L - p.R) * coupling / 4) := by
    calc
      _ = P * (coupling ^ 9 * Real.exp (-coupling * J)) := by
        change K * c ^ 2 * Γ ^ 2 * coupling ^ 15 * Real.exp (-2 * coupling * (G + J)) = _
        rw [hsplit]
        dsimp [P]
        ring
      _ ≤ P * (coupling ^ 9 * Real.exp (-a * coupling)) := by
        gcongr
      _ ≤ P * (S ^ 2 * Real.exp (-(a / 2) * coupling)) :=
        mul_le_mul_of_nonneg_left hscalar hP
      _ ≤ (P * Real.sqrt coupling) * (S ^ 2 * Real.exp (-(a / 2) * coupling)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt hP
      _ = _ := by
        dsimp [P, S, A, a, activeSaddleEnvelope]
        rw [show -((2 * L - p.R) / 2 / 2) * coupling =
          -(2 * L - p.R) * coupling / 4 by ring]
        field_simp [hp.ε_pos.ne', hp.a_pos.ne']
  calc
    _ ≤ (K / (p.ε ^ 2 * p.a ^ 2)) * p.activeSaddleEnvelope L coupling c Γ *
        Real.exp (-(2 * L - p.R) * coupling / 4) := hGaussian
    _ ≤ (K / (p.ε ^ 2 * p.a ^ 2)) * (2 * p.activeSaddleTexEnvelope L coupling c Γ) *
        Real.exp (-(2 * L - p.R) * coupling / 4) := by
      gcongr
    _ = _ := by ring

theorem exists_oppositeSupportBound_le_activeSaddleTexEnvelope_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L K : ℝ} (hL : p.R < L) (hK : 0 ≤ K) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ c : ℝ, 0 < c → ∀ Γ : ℝ, 0 < Γ →
        0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
        p.oppositeSupportFineBound L K coupling c Γ ≤
          (2 * K / (p.ε ^ 2 * p.a ^ 2)) *
            p.activeSaddleTexEnvelope L coupling c Γ *
              Real.exp (-(2 * L - p.R) * coupling / 4) := by
  obtain ⟨T, hT, hbound⟩ := exists_oppositeSupportBound_le_activeSaddleTexEnvelope hp hL hK
  obtain ⟨Te, _hTe, henergy⟩ := exists_scaledAtomicEnergy_pos_of_radialData hp hRad hAcore hApot
  refine ⟨max T Te, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  exact hbound coupling ((le_max_left _ _).trans hc)
    (henergy coupling ((le_max_right _ _).trans hc)).1

/-- The coefficients may vary arbitrarily: their eventual positivity is
enough, because exactly the same coefficients occur in both expressions. -/
theorem oppositeSupportFineBound_isLittleO_activeSaddleTexEnvelope_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L K : ℝ} (hL : p.R < L) (hK : 0 ≤ K)
    {c Γ : ℝ → ℝ} (hc : ∀ᶠ coupling in atTop, 0 < c coupling)
    (hΓ : ∀ᶠ coupling in atTop, 0 < Γ coupling) :
    (fun coupling => p.oppositeSupportFineBound L K coupling (c coupling) (Γ coupling))
      =o[atTop] (fun coupling =>
        p.activeSaddleTexEnvelope L coupling (c coupling) (Γ coupling)) := by
  obtain ⟨T, hT, hbound⟩ :=
    exists_oppositeSupportBound_le_activeSaddleTexEnvelope_of_radialData
      hp hRad hAcore hApot hL hK
  have hR : 0 < p.R := by linarith [hp.radius_large, hp.r₀_pos]
  have hd : -(2 * L - p.R) / 4 < 0 := by linarith
  have he := Real.tendsto_exp_atBot.comp
    ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop_of_neg hd)
  have hrate : Tendsto (fun coupling : ℝ =>
      (2 * K / (p.ε ^ 2 * p.a ^ 2)) * Real.exp (-(2 * L - p.R) * coupling / 4))
      atTop (𝓝 0) := by
    convert he.const_mul (2 * K / (p.ε ^ 2 * p.a ^ 2)) using 1
    · ext coupling
      dsimp
      congr 2
      ring
    · simp only [mul_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_ge_atTop T, hc, hΓ,
    hrate.eventually (gt_mem_nhds hε)] with coupling hcoupling hcc hΓc hratec
  obtain ⟨henv, hle⟩ := hbound coupling hcoupling (c coupling) hcc (Γ coupling) hΓc
  have hcpos : 0 < coupling := hT.trans_le hcoupling
  have hnonneg : 0 ≤ p.oppositeSupportFineBound L K coupling (c coupling) (Γ coupling) := by
    dsimp [oppositeSupportFineBound]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs, abs_of_pos henv]
  calc
    _ ≤ ((2 * K / (p.ε ^ 2 * p.a ^ 2)) *
        Real.exp (-(2 * L - p.R) * coupling / 4)) *
          p.activeSaddleTexEnvelope L coupling (c coupling) (Γ coupling) := by
      nlinarith only [hle]
    _ ≤ _ := mul_le_mul_of_nonneg_right hratec.le henv.le

end InfiniteZero.CuspParameters
