import InfiniteZero.LogFlatStretchedErrors

/-! Stretched exponential errors absorb polynomial semiclassical prefactors,
including after both normal saddle factors are applied. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero

theorem tendsto_inv_pow_mul_stretched_exp {d q : ℝ} (hd : 0 < d) (hq : 0 < q) (N : ℕ) :
    Tendsto (fun h : ℝ => (h ^ N)⁻¹ *
      Real.exp (-d * Real.exp (q * Real.log (1 / h)))) (𝓝[>] 0) (𝓝 0) := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hlim := (tendsto_pow_mul_exp_sq_sub_exp (N : ℝ) hd hq 0).comp hlog
  simp only [Function.comp_def, pow_zero, one_mul] at hlim
  apply squeeze_zero'
    (g := fun h : ℝ => Real.exp ((N : ℝ) * Real.log (1 / h) ^ 2 -
      d * Real.exp (q * Real.log (1 / h)))) ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hhpos : 0 < h := hh
    positivity
  · filter_upwards [self_mem_nhdsWithin, hlog.eventually (eventually_ge_atTop (1 : ℝ))]
      with h hh hℓ
    have hhpos : 0 < h := hh
    have he : (h ^ N)⁻¹ = Real.exp ((N : ℝ) * Real.log (1 / h)) := by
      rw [Real.exp_nat_mul, Real.exp_log (one_div_pos.mpr hhpos)]
      simp only [one_div, inv_pow]
    rw [he, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp : Real.log (1 / h) ≤ Real.log (1 / h) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ N by positivity)
    linarith

theorem tendsto_logFlatSaddle_normalized_polynomial_stretched_error
    {β k tStar d q : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (hd : 0 < d) (hq : 0 < q) (N : ℕ) :
    Tendsto (fun h : ℝ => ‖logFlatSaddleNormalizer β k tStar c h‖ * (h ^ N)⁻¹ *
      Real.exp (-d * Real.exp (q * Real.log (1 / h)))) (𝓝[>] 0) (𝓝 0) := by
  have hn := tendsto_logFlatSaddle_normalized_stretched_error (k := k) hβ ht hc (half_pos hd) hq
  have hp := tendsto_inv_pow_mul_stretched_exp (half_pos hd) hq N
  have hl := hn.mul hp
  simp only [mul_zero] at hl
  apply hl.congr
  intro h
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

theorem tendsto_logFlatSaddleProduct_normalized_polynomial_stretched_error
    {β k tStar d q : ℝ} {c₁ c₂ : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hd : 0 < d) (hq : 0 < q) (N : ℕ) :
    Tendsto (fun h : ℝ =>
      ‖logFlatSaddleNormalizer β k tStar c₁ h * logFlatSaddleNormalizer β k tStar c₂ h‖ *
        (h ^ N)⁻¹ * Real.exp (-d * Real.exp (q * Real.log (1 / h))))
      (𝓝[>] 0) (𝓝 0) := by
  have hd3 : 0 < d / 3 := by positivity
  have h1 := tendsto_logFlatSaddle_normalized_stretched_error (k := k) hβ ht hc₁ hd3 hq
  have h2 := tendsto_logFlatSaddle_normalized_stretched_error (k := k) hβ ht hc₂ hd3 hq
  have hp := tendsto_inv_pow_mul_stretched_exp hd3 hq N
  have hl := (h1.mul h2).mul hp
  simp only [mul_zero] at hl
  apply hl.congr
  intro h
  rw [norm_mul]
  calc
    _ = (‖logFlatSaddleNormalizer β k tStar c₁ h‖ *
      ‖logFlatSaddleNormalizer β k tStar c₂ h‖ * (h ^ N)⁻¹) *
      (Real.exp (-(d / 3) * Real.exp (q * Real.log (1 / h))) *
        Real.exp (-(d / 3) * Real.exp (q * Real.log (1 / h))) *
        Real.exp (-(d / 3) * Real.exp (q * Real.log (1 / h)))) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

end InfiniteZero
