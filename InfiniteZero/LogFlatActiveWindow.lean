import InfiniteZero.LogFlatStretchedErrors

/-!
# A wider active normal window sufficient for relative o(1)

We choose tStar * h^(3/4), instead of M*h*log(1/h). Quadratic phase
remainders divided by h vanish, while discarded pieces decay at scale
exp(-d*h^(-1/4)), still negligible after the true saddle normalization.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

def logFlatActiveLogCut (h : ℝ) : ℝ := (3 / 4 : ℝ) * Real.log (1 / h)

def logFlatActiveWindow (tStar h : ℝ) : ℝ := tStar * Real.exp (-logFlatActiveLogCut h)

theorem logFlatActiveWindow_pos {tStar : ℝ} (ht : 0 < tStar) (h : ℝ) :
    0 < logFlatActiveWindow tStar h := mul_pos ht (Real.exp_pos _)

theorem logFlatActiveWindow_eq_rpow (tStar : ℝ) {h : ℝ} (hh : 0 < h) :
    logFlatActiveWindow tStar h = tStar * h ^ (3 / 4 : ℝ) := by
  rw [logFlatActiveWindow, logFlatActiveLogCut, Real.rpow_def_of_pos hh]
  rw [one_div, Real.log_inv]
  congr 2
  ring

theorem tendsto_logFlatActiveWindow (tStar : ℝ) :
    Tendsto (logFlatActiveWindow tStar) (𝓝[>] 0) (𝓝 0) := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hexp : Tendsto (fun h : ℝ => Real.exp (-(3 / 4 : ℝ) * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (by norm_num))
  simpa only [logFlatActiveWindow, logFlatActiveLogCut, neg_mul, mul_zero] using hexp.const_mul tStar

theorem logFlatActiveWindow_div (tStar : ℝ) {h : ℝ} (hh : 0 < h) :
    logFlatActiveWindow tStar h / h =
      tStar * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)) := by
  have he : Real.exp (Real.log (1 / h)) = h⁻¹ := by
    rw [Real.exp_log (one_div_pos.mpr hh), one_div]
  rw [logFlatActiveWindow, logFlatActiveLogCut, div_eq_mul_inv, ← he, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem logFlatActiveWindow_sq_div (tStar : ℝ) {h : ℝ} (hh : 0 < h) :
    logFlatActiveWindow tStar h ^ 2 / h =
      tStar ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.log (1 / h)) := by
  have he : Real.exp (Real.log (1 / h)) = h⁻¹ := by
    rw [Real.exp_log (one_div_pos.mpr hh), one_div]
  rw [logFlatActiveWindow, logFlatActiveLogCut, mul_pow, sq (Real.exp _), ← Real.exp_add,
    div_eq_mul_inv, ← he, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem tendsto_logFlatActiveWindow_sq_div (tStar : ℝ) :
    Tendsto (fun h => logFlatActiveWindow tStar h ^ 2 / h) (𝓝[>] 0) (𝓝 0) := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hexp : Tendsto (fun h : ℝ => Real.exp (-(1 / 2 : ℝ) * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (by norm_num))
  apply (show Tendsto (fun h => tStar ^ 2 * Real.exp (-(1 / 2 : ℝ) * Real.log (1 / h)))
    (𝓝[>] 0) (𝓝 0) by simpa using hexp.const_mul (tStar ^ 2)).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (logFlatActiveWindow_sq_div tStar hh).symm

theorem logFlatActiveWindow_log_ratio {tStar : ℝ} (ht : 0 < tStar) (h : ℝ) :
    Real.log (tStar / logFlatActiveWindow tStar h) = logFlatActiveLogCut h := by
  rw [logFlatActiveWindow, div_mul_cancel_left₀ ht.ne', ← Real.exp_neg, Real.log_exp, neg_neg]

theorem logFlatActiveWindow_error_rate (tStar : ℝ) (c : ℂ) {h : ℝ} (hh : 0 < h) :
    logFlatContourErrorRate tStar c (logFlatActiveLogCut h) / h =
      (tStar * c.re) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)) := by
  unfold logFlatContourErrorRate
  change (logFlatActiveWindow tStar h * c.re) / h = _
  rw [mul_div_right_comm, logFlatActiveWindow_div tStar hh]
  ring

/-- The actual critical point lies well inside the wider window. -/
theorem tendsto_logFlatSaddle_location_div_window {β k tStar : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : 0 < tStar) (hc : c ≠ 0) :
    Tendsto (fun h : ℝ =>
      ‖(tStar : ℂ) * Complex.exp (-logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))‖ /
        logFlatActiveWindow tStar h) (𝓝[>] 0) (𝓝 0) := by
  let C := (4 * |β| / ‖c‖) / tStar
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hdecay : Tendsto (fun ℓ : ℝ => ℓ * Real.exp (-(1 / 4 : ℝ) * ℓ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 4 : ℝ) (by norm_num)
  apply squeeze_zero'
    (g := fun h : ℝ => C * (Real.log (1 / h) * Real.exp (-(1 / 4 : ℝ) * Real.log (1 / h))))
    ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun h => div_nonneg (norm_nonneg _) (logFlatActiveWindow_pos ht h).le
  · filter_upwards [eventually_logFlatSaddle_location_bound (k := k) hβ ht.ne' hc,
      self_mem_nhdsWithin] with h hbound hh
    have hhpos : 0 < h := hh
    apply (div_le_div_of_nonneg_right hbound (logFlatActiveWindow_pos ht h).le).trans_eq
    have hr := logFlatActiveWindow_div tStar hhpos
    have he : h / logFlatActiveWindow tStar h =
        tStar⁻¹ * Real.exp (-(1 / 4 : ℝ) * Real.log (1 / h)) := by
      have hinv := congrArg Inv.inv hr
      simpa only [inv_div, mul_inv_rev, ← Real.exp_neg, mul_comm, neg_mul] using hinv
    calc
      _ = (4 * |β| / ‖c‖) * (h / logFlatActiveWindow tStar h) * Real.log (1 / h) := by ring
      _ = _ := by rw [he]; dsimp [C]; ring
  · simpa only [Function.comp_def, mul_zero] using (hdecay.comp hlog).const_mul C

end InfiniteZero
