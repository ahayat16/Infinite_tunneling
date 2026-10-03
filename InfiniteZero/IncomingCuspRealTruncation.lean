import InfiniteZero.IncomingCuspDensityBound
import InfiniteZero.NormalBoxTruncation
import InfiniteZero.ActiveSaddleEnvelope

/-!
# Real truncation of the physical incoming density

The density retains its true core and full energies. Its exact radial
action cancels only against the displayed normalization; the tail gain
comes from the actual normal coordinates. All estimates are uniform in
the two energies and both tangent coordinates on their specified ranges.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem exists_incomingCuspDensity_plain_bound {p : CuspParameters}
    (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ Ec ∈ Icc (1 / 2 : ℝ) 1, ∀ Ef ∈ Icc (1 / 2 : ℝ) 1,
      ∀ h > 0, h ≤ 1 → ∀ t ∈ Icc 0 p.t₀, ∀ u ∈ Icc 0 p.t₀,
      ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ‖p.incomingCuspDensity L h Ec Ef t u s r‖ ≤
        (C * (h ^ 6)⁻¹ * Real.exp (-p.activeReferenceAction L Ef Ec / h)) *
          t ^ 2 * u ^ 2 * Real.exp (-(1 / 8 : ℝ) * (t + u) / h) := by
  obtain ⟨C, hC, hbound⟩ := exists_incomingCuspDensity_bound hp hL
  refine ⟨C, hC, ?_⟩
  intro Ec hEc Ef hEf h hh hh1 t ht u hu s r hs hr
  have hflat (v : ℝ) : 0 ≤ logFlat p.β p.tStar v ∧ logFlat p.β p.tStar v ≤ 1 := by
    unfold logFlat
    split_ifs
    · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
        (by nlinarith [sq_nonneg (Real.log (p.tStar / v)), hp.β_pos])⟩
    · norm_num
  have he : Real.exp (-t / (8 * h)) * Real.exp (-u / (8 * h)) =
      Real.exp (-(1 / 8 : ℝ) * (t + u) / h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (hbound Ec hEc Ef hEf h hh hh1 t ht u hu s r hs hr).trans
  calc
    _ ≤ C * (h ^ 6)⁻¹ * Real.exp (-p.activeReferenceAction L Ef Ec / h) *
        (t ^ 2 * 1 * Real.exp (-t / (8 * h))) *
        (u ^ 2 * 1 * Real.exp (-u / (8 * h))) := by
      gcongr
      · exact mul_nonneg (mul_nonneg (sq_nonneg _) (hflat u).1) (Real.exp_pos _).le
      · exact (hflat t).2
      · exact (hflat u).2
    _ = _ := by
      simp only [mul_one]
      calc
        _ = (C * (h ^ 6)⁻¹ * Real.exp (-p.activeReferenceAction L Ef Ec / h)) *
            t ^ 2 * u ^ 2 * (Real.exp (-t / (8 * h)) * Real.exp (-u / (8 * h))) := by ring
        _ = _ := by rw [he]

theorem exists_incomingCuspDensity_truncation_bound {p : CuspParameters}
    (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ Ec ∈ Icc (1 / 2 : ℝ) 1, ∀ Ef ∈ Icc (1 / 2 : ℝ) 1,
      ∀ h > 0, h ≤ 1 → ∀ T > 0, T ≤ p.t₀ →
      ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ‖(∫ q in positiveNormalBox p.t₀, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) -
        (∫ q in positiveNormalBox T, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r)‖ ≤
        C * (h ^ 6)⁻¹ * Real.exp (-p.activeReferenceAction L Ef Ec / h) *
          p.t₀ ^ 6 * Real.exp (-(1 / 8 : ℝ) * T / h) := by
  obtain ⟨C, hC, hbound⟩ := exists_incomingCuspDensity_plain_bound hp hL
  refine ⟨C, hC, ?_⟩
  intro Ec hEc Ef hEf h hh hh1 T hT hTt s r hs hr
  have hi := integrableOn_incomingCuspDensity_normals hp hL hh
    (lt_of_lt_of_le (by norm_num) hEc.1) (lt_of_lt_of_le (by norm_num) hEf.1)
    (abs_le.mp hs) (abs_le.mp hr)
  apply norm_integral_sub_positiveNormalBox_le hp.t₀_pos hT hTt
    (by norm_num : (0 : ℝ) ≤ 1 / 8) hh (by positivity) hi
  intro q hq
  exact hbound Ec hEc Ef hEf h hh hh1 q.1 ⟨hq.1.1.le, hq.1.2.le⟩
    q.2 ⟨hq.2.1.le, hq.2.2.le⟩ s r hs hr

/-- The true real tail is negligible with both complex normalizers, uniformly
in the two energies and tangent coordinates. Only the main radial action
is removed here; the kernel leading coefficients are treated separately. -/
theorem eventually_incomingCuspDensity_action_normalized_truncation
    {p : CuspParameters} (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ Ec ∈ Icc (1 / 2 : ℝ) 1,
      ∀ Ef ∈ Icc (1 / 2 : ℝ) 1, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
        ((Real.exp (p.activeReferenceAction L Ef Ec / h) : ℂ) *
          ((∫ q in positiveNormalBox p.t₀, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) -
            (∫ q in positiveNormalBox (logFlatActiveWindow p.tStar h),
              p.incomingCuspDensity L h Ec Ef q.1 q.2 s r)))‖ < ε := by
  obtain ⟨C, hC, hbound⟩ := exists_incomingCuspDensity_plain_bound hp hL
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hb := eventually_normalized_positiveNormalBox_truncation
    (k := (2 : ℝ)) hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) hp.t₀_pos
    (by norm_num : (0 : ℝ) < 1 / 8) (activeSaddleSlope_ne_zero hp L) 6 hδ
  filter_upwards [hb, self_mem_nhdsWithin,
    (show ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 from
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with h hb hh hh1
  intro Ec hEc Ef hEf s r hs hr
  let A := p.activeReferenceAction L Ef Ec / h
  let F : ℝ × ℝ → ℂ := fun q =>
    (Real.exp A : ℂ) * p.incomingCuspDensity L h Ec Ef q.1 q.2 s r
  have hi := (integrableOn_incomingCuspDensity_normals hp hL hh
    (lt_of_lt_of_le (by norm_num) hEc.1) (lt_of_lt_of_le (by norm_num) hEf.1)
    (abs_le.mp hs) (abs_le.mp hr)).const_mul (Real.exp A : ℂ)
  have he : Real.exp A * Real.exp (-p.activeReferenceAction L Ef Ec / h) = 1 := by
    rw [← Real.exp_add]
    rw [show A + -p.activeReferenceAction L Ef Ec / h = 0 by dsimp [A]; ring]
    exact Real.exp_zero
  have hpoint : ∀ q ∈ positiveNormalBox p.t₀,
      ‖F q‖ ≤ C * (h ^ 6)⁻¹ * q.1 ^ 2 * q.2 ^ 2 *
        Real.exp (-(1 / 8 : ℝ) * (q.1 + q.2) / h) := by
    intro q hq
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp A * ((C * (h ^ 6)⁻¹ * Real.exp (-p.activeReferenceAction L Ef Ec / h)) *
          q.1 ^ 2 * q.2 ^ 2 * Real.exp (-(1 / 8 : ℝ) * (q.1 + q.2) / h)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hbound Ec hEc Ef hEf h hh hh1.le q.1 ⟨hq.1.1.le, hq.1.2.le⟩
          q.2 ⟨hq.2.1.le, hq.2.2.le⟩ s r hs hr
      _ = _ := by
        calc
          _ = (Real.exp A * Real.exp (-p.activeReferenceAction L Ef Ec / h)) *
              (C * (h ^ 6)⁻¹ * q.1 ^ 2 * q.2 ^ 2 *
                Real.exp (-(1 / 8 : ℝ) * (q.1 + q.2) / h)) := by ring
          _ = _ := by rw [he, one_mul]
  have hn := hb C hC.le F hi hpoint
  have hsmall : ε / (C + 1) * C < ε := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr
    nlinarith
  apply lt_of_le_of_lt _ hsmall
  simpa only [F, integral_const_mul, ← mul_sub, A] using hn

end InfiniteZero.CuspParameters
