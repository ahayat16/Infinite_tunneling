import InfiniteZero.ComplexLogFlatCutoffAsymptotic

/-!
# Stretched exponential errors at the log-flat saddle

Errors at scale exp(-d h^(-q)), q>0, are sufficient for the main theorem.
This permits a wider shrinking normal window than h log(1/h).
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

theorem tendsto_pow_mul_exp_sq_sub_exp (C : ℝ) {d q : ℝ}
    (hd : 0 < d) (hq : 0 < q) (N : ℕ) :
    Tendsto (fun ℓ : ℝ => ℓ ^ N * Real.exp (C * ℓ ^ 2 - d * Real.exp (q * ℓ)))
      atTop (𝓝 0) := by
  have hB : 0 < |C| + 1 := by positivity
  have hsmall := (isLittleO_pow_exp_pos_mul_atTop 2 hq).bound (div_pos hd hB)
  apply squeeze_zero'
    (g := fun ℓ : ℝ => ℓ ^ N * Real.exp (-ℓ ^ 2)) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ℓ hℓ
    positivity
  · filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with ℓ hsmall hℓ
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ℓ),
      abs_of_pos (Real.exp_pos _)] at hsmall
    have hbound : (|C| + 1) * ℓ ^ 2 ≤ d * Real.exp (q * ℓ) := by
      calc
        _ ≤ (|C| + 1) * ((d / (|C| + 1)) * Real.exp (q * ℓ)) :=
          mul_le_mul_of_nonneg_left hsmall hB.le
        _ = _ := by field_simp
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hℓ N)
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg ℓ)]
  · simpa only [neg_mul, one_mul, zero_mul, add_zero] using
      tendsto_pow_mul_exp_quadratic (show (0 : ℝ) < 1 by norm_num) 0 N

theorem tendsto_logFlatSaddle_normalized_stretched_error {β k tStar d q : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) (hd : 0 < d) (hq : 0 < q) :
    Tendsto (fun h : ℝ => ‖logFlatSaddleNormalizer β k tStar c h‖ *
      Real.exp (-d * Real.exp (q * Real.log (1 / h)))) (𝓝[>] 0) (𝓝 0) := by
  let C := 8 * β + |(k + 1) ^ 2 / (4 * β)|
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  apply squeeze_zero'
    (g := fun h : ℝ => 2 * (Real.log (1 / h) ^ 1 *
      Real.exp (C * Real.log (1 / h) ^ 2 - d * Real.exp (q * Real.log (1 / h))))) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun h => by positivity
  · filter_upwards [eventually_norm_logFlatSaddle_value_le (k := k) hβ ht hc,
      eventually_sqrt_re_logFlatSaddleRoot_le β k tStar c] with h hv hs
    simp only [logFlatSaddleNormalizer, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
    rw [mul_assoc, ← Real.exp_add]
    have he : (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))).re ≤
        C * Real.log (1 / h) ^ 2 := (Complex.re_le_norm _).trans hv
    calc
      _ ≤ (2 * Real.log (1 / h)) * Real.exp (C * Real.log (1 / h) ^ 2 -
          d * Real.exp (q * Real.log (1 / h))) := by
        apply mul_le_mul hs (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        linarith [Real.sqrt_nonneg (logFlatSaddleRoot β k tStar c h).re]
      _ = _ := by simp only [pow_one, mul_assoc]
  · simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_mul_exp_sq_sub_exp C hd hq 1).comp hlog).const_mul 2

theorem tendsto_logFlatSaddle_normalized_stretched_remainder
    {β k tStar d q M : ℝ} {c : ℂ} {r : ℝ → ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) (hd : 0 < d) (hq : 0 < q)
    (hr : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖r h‖ ≤ M * Real.exp (-d * Real.exp (q * Real.log (1 / h)))) :
    Tendsto (fun h => logFlatSaddleNormalizer β k tStar c h * r h) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm'
    (a := fun h => M * (‖logFlatSaddleNormalizer β k tStar c h‖ *
      Real.exp (-d * Real.exp (q * Real.log (1 / h))))) ?_ ?_
  · filter_upwards [hr] with h hh
    rw [norm_mul]
    calc
      _ ≤ ‖logFlatSaddleNormalizer β k tStar c h‖ *
          (M * Real.exp (-d * Real.exp (q * Real.log (1 / h)))) :=
        mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = _ := by ring
  · simpa only [mul_zero] using
      (tendsto_logFlatSaddle_normalized_stretched_error (k := k) hβ ht hc hd hq).const_mul M

end InfiniteZero
