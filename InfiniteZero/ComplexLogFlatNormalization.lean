import InfiniteZero.ComplexLogFlatSaddle
import InfiniteZero.LogFlat
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponentially small errors survive the actual saddle normalization

The value of the phase at the constructed complex saddle grows at most
quadratically in `log (1/h)`. Every fixed error `exp (-d/h)`, `d > 0`,
therefore remains negligible after multiplication by the complex saddle
exponential and the square-root Gaussian normalization.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

/-- Exponential decay at scale `1/h` absorbs a quadratic logarithmic
exponential and any fixed natural power of the logarithm. -/
theorem tendsto_log_pow_mul_exp_log_sq_sub_div (C : ℝ) {d : ℝ}
    (hd : 0 < d) (N : ℕ) :
    Tendsto (fun h : ℝ => (Real.log (1 / h)) ^ N *
      Real.exp (C * (Real.log (1 / h)) ^ 2 - d / h)) (𝓝[>] 0) (𝓝 0) := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hB : 0 < |C| + 1 := by positivity
  have hsmall := (isLittleO_pow_exp_pos_mul_atTop 2 (show (0 : ℝ) < 1 by norm_num)).bound
    (div_pos hd hB)
  have hnonneg := hlog.eventually (eventually_ge_atTop (0 : ℝ))
  apply squeeze_zero'
    (g := fun h : ℝ => (Real.log (1 / h)) ^ N * Real.exp (-(Real.log (1 / h)) ^ 2))
    ?_ ?_ ?_
  · filter_upwards [hnonneg] with h hh
    exact mul_nonneg (pow_nonneg hh N) (Real.exp_pos _).le
  · filter_upwards [hlog.eventually hsmall, hnonneg, self_mem_nhdsWithin] with h hsmall hh hhpos
    have hhpos' : 0 < h := hhpos
    simp only [Real.norm_eq_abs, one_mul, Real.exp_log (one_div_pos.mpr hhpos'),
      abs_of_nonneg (sq_nonneg (Real.log (1 / h))),
      abs_of_pos (one_div_pos.mpr hhpos')] at hsmall
    have hbound : (|C| + 1) * (Real.log (1 / h)) ^ 2 ≤ d / h := by
      calc
        _ ≤ (|C| + 1) * ((d / (|C| + 1)) * (1 / h)) :=
          mul_le_mul_of_nonneg_left hsmall hB.le
        _ = d / h := by field_simp
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hh N)
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg (Real.log (1 / h)))]
  · simpa only [Function.comp_def, neg_mul, one_mul, zero_mul, add_zero] using
      (tendsto_pow_mul_exp_quadratic (show (0 : ℝ) < 1 by norm_num) 0 N).comp hlog

/-- A coarse bound on the full complex critical value; in particular it
controls its real part, without assuming the saddle equation. -/
theorem eventually_norm_logFlatSaddle_value_le {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))‖ ≤
        (8 * β + |(k + 1) ^ 2 / (4 * β)|) * (Real.log (1 / h)) ^ 2 := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_logFlatSaddleRoot_value_hessian (k := k) hβ.ne' ht.ne' hc,
    eventually_norm_logFlatSaddleRoot_le β k tStar c,
    hlog.eventually (eventually_ge_atTop (1 : ℝ))] with h hvalue hnorm hlarge
  let w := logFlatSaddleRoot β k tStar c h
  let ℓ := Real.log (1 / h)
  have hℓ : 1 ≤ ℓ := hlarge
  have hn : ‖w‖ ≤ 2 * ℓ := hnorm
  rw [hvalue.1]
  calc
    _ ≤ ‖(β : ℂ) * (w ^ 2 + 2 * w)‖ + ‖(((k + 1) ^ 2 / (4 * β) : ℝ) : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ β * (‖w‖ ^ 2 + 2 * ‖w‖) + |(k + 1) ^ 2 / (4 * β)| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ,
        Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exact (norm_add_le (w ^ 2) (2 * w)).trans (add_le_add (norm_pow_le w 2)
        (by rw [norm_mul]; norm_num))
    _ ≤ (8 * β + |(k + 1) ^ 2 / (4 * β)|) * ℓ ^ 2 := by
      have hsq : ‖w‖ ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith [norm_nonneg w]
      have hpow : 1 ≤ ℓ ^ 2 := by nlinarith
      have hlinear : ℓ ≤ ℓ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hβ.le,
        mul_le_mul_of_nonneg_left hn hβ.le,
        mul_le_mul_of_nonneg_left hlinear hβ.le,
        mul_le_mul_of_nonneg_left hpow (abs_nonneg ((k + 1) ^ 2 / (4 * β)))]

theorem eventually_sqrt_re_logFlatSaddleRoot_le (β k tStar : ℝ) (c : ℂ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      Real.sqrt (logFlatSaddleRoot β k tStar c h).re ≤ 2 * Real.log (1 / h) := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_norm_logFlatSaddleRoot_le β k tStar c,
    hlog.eventually (eventually_ge_atTop (1 : ℝ))] with h hn hℓ
  have hre := (Complex.re_le_norm (logFlatSaddleRoot β k tStar c h)).trans hn
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · nlinarith

/-- The actual saddle normalization preserves every fixed `exp (-d/h)`
error. All parameters of the saddle are fixed before `h` tends to zero. -/
theorem tendsto_logFlatSaddle_normalized_exp_error {β k tStar d : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) (hd : 0 < d) :
    Tendsto (fun h : ℝ => Real.sqrt (logFlatSaddleRoot β k tStar c h).re *
      ‖Complex.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)))‖ *
      Real.exp (-d / h)) (𝓝[>] 0) (𝓝 0) := by
  let C := 8 * β + |(k + 1) ^ 2 / (4 * β)|
  apply squeeze_zero'
    (g := fun h : ℝ => 2 * ((Real.log (1 / h)) ^ 1 *
      Real.exp (C * (Real.log (1 / h)) ^ 2 - d / h))) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun h => by positivity
  · filter_upwards [eventually_norm_logFlatSaddle_value_le (k := k) hβ ht hc,
      eventually_sqrt_re_logFlatSaddleRoot_le β k tStar c] with h hv hs
    rw [Complex.norm_exp, mul_assoc, ← Real.exp_add]
    have he : (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))).re ≤
        C * (Real.log (1 / h)) ^ 2 := (Complex.re_le_norm _).trans hv
    calc
      _ ≤ (2 * Real.log (1 / h)) * Real.exp (C * (Real.log (1 / h)) ^ 2 - d / h) := by
        apply mul_le_mul hs (Real.exp_le_exp.mpr (by
          simpa only [neg_div, sub_eq_add_neg, add_comm] using add_le_add_right he (-(d / h))))
          (Real.exp_pos _).le
        linarith [Real.sqrt_nonneg (logFlatSaddleRoot β k tStar c h).re]
      _ = _ := by simp only [pow_one, mul_assoc]
  · simpa only [mul_zero] using (tendsto_log_pow_mul_exp_log_sq_sub_div C hd 1).const_mul 2

/-- A complex remainder with a fixed exponential bound becomes negligible
after the actual complex saddle normalization. -/
theorem tendsto_logFlatSaddle_normalized_remainder {β k tStar d M : ℝ} {c : ℂ}
    {r : ℝ → ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) (hd : 0 < d)
    (hr : ∀ᶠ h : ℝ in 𝓝[>] 0, ‖r h‖ ≤ M * Real.exp (-d / h)) :
    Tendsto (fun h : ℝ => (Real.sqrt (logFlatSaddleRoot β k tStar c h).re : ℂ) *
      Complex.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))) * r h)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
    (g := fun h : ℝ => M * (Real.sqrt (logFlatSaddleRoot β k tStar c h).re *
      ‖Complex.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)))‖ *
      Real.exp (-d / h))) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [hr] with h hh
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (logFlatSaddleRoot β k tStar c h).re *
          ‖Complex.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
            (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)))‖ *
          (M * Real.exp (-d / h)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  · simpa only [mul_zero] using
      (tendsto_logFlatSaddle_normalized_exp_error (k := k) hβ ht hc hd).const_mul M

end InfiniteZero
