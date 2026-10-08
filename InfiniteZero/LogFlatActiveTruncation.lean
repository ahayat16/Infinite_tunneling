import InfiniteZero.LogFlatActiveWindow

/-! Actual moving contours and normal integrals on the h^(3/4) window. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

/-- The branch threshold is independent of the real endpoint of the contour. -/
theorem eventually_forall_logFlatContour_errors_le {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ,
      Integrable (fun x : ℝ => logFlatContourFunction β k tStar c h
        ((x : ℂ) + ((logFlatSaddleRoot β k tStar c h).im : ℂ) * Complex.I)) ∧
      ‖logFlatRayError β k tStar c a h‖ ≤
        ((Real.pi + Real.sqrt (Real.pi / (β / 2))) * logFlatErrorMajorant β k) *
          Real.exp (-logFlatContourErrorRate tStar c a / h) := by
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  filter_upwards [eventually_logFlatSaddleRoot_connector_re (k := k) hβ ht hc,
    eventually_logFlatSaddleRoot_arg (k := k) hβ ht hcne, self_mem_nhdsWithin]
    with h hrot harg hh
  intro a
  have hhpos : 0 < h := hh
  have hv : |(logFlatSaddleRoot β k tStar c h).im| ≤ Real.pi :=
    harg.2.2.trans (Complex.abs_arg_le_pi c)
  have hrv := hrot _ right_mem_uIcc
  refine ⟨integrable_logFlatContourFunction_horizontal hβ ht.le hhpos hv
    (hc.le.trans hrv) k, ?_⟩
  have h1 := norm_integral_logFlatContourFunction_connector_le hβ ht hhpos hv hc hrot k a
  have h2 := norm_integral_logFlatContourFunction_left_le hβ ht hhpos hv hc hrv k a
  unfold logFlatRayError
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul]
  change ‖∫ η in 0..(logFlatSaddleRoot β k tStar c h).im,
    logFlatContourFunction β k tStar c h ((a : ℂ) + (η : ℂ) * Complex.I)‖ +
    ‖∫ x in Iic a, logFlatContourFunction β k tStar c h
      ((x : ℂ) + ((logFlatSaddleRoot β k tStar c h).im : ℂ) * Complex.I)‖ ≤ _
  nlinarith

theorem tendsto_logFlatActiveRayError_normalized {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer β k tStar c h *
      logFlatRayError β k tStar c (logFlatActiveLogCut h) h) (𝓝[>] 0) (𝓝 0) := by
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  apply tendsto_logFlatSaddle_normalized_stretched_remainder hβ ht hcne
    (mul_pos ht hc) (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [eventually_forall_logFlatContour_errors_le (k := k) hβ ht hc,
    self_mem_nhdsWithin] with h hs hh
  have hb := (hs (logFlatActiveLogCut h)).2
  simpa only [neg_div, logFlatActiveWindow_error_rate tStar c hh, neg_mul] using hb

theorem tendsto_logFlatActiveRay_normalized {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer β k tStar c h *
      (∫ x in Ioi (logFlatActiveLogCut h),
        logFlatComplexIntegrand β k (c * (tStar : ℂ) / (h : ℂ)) (x : ℂ)))
      (𝓝[>] 0) (𝓝 ((Real.sqrt (Real.pi / β) : ℝ) : ℂ)) := by
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  have hsum := (tendsto_logFlatSaddle_horizontal_leading (k := k) hβ ht hcne).add
    (tendsto_logFlatActiveRayError_normalized (k := k) hβ ht hc)
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_forall_logFlatContour_errors_le (k := k) hβ ht hc] with h hs
  rw [logFlatComplex_ray_eq_saddle_add_error hβ k tStar c (logFlatActiveLogCut h) h
    (hs (logFlatActiveLogCut h)).1, mul_add]
  rfl

theorem tendsto_complexLogFlatActiveIntegral_normalized {β tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) (m : ℕ) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer β (m : ℝ) tStar c h *
      (∫ t in Ioo 0 (logFlatActiveWindow tStar h), complexLogFlatIntegrand β tStar h c m t))
      (𝓝[>] 0) (𝓝 ((tStar : ℂ) ^ (m + 1) * ((Real.sqrt (Real.pi / β) : ℝ) : ℂ))) := by
  have hlim := (tendsto_logFlatActiveRay_normalized (k := (m : ℝ)) hβ ht hc).const_mul
    ((tStar : ℂ) ^ (m + 1))
  apply hlim.congr
  intro h
  rw [integral_complexLogFlat_logarithmic_change ht (logFlatActiveWindow_pos ht h),
    logFlatActiveWindow_log_ratio ht h]
  dsimp only [logFlatComplexIntegrand]
  ring

theorem norm_logarithmicPoint_le_activeWindow {tStar h x : ℝ} (ht : 0 < tStar)
    (hx : logFlatActiveLogCut h ≤ x) (η : ℝ) :
    ‖(tStar : ℂ) * Complex.exp (-((x : ℂ) + (η : ℂ) * Complex.I))‖ ≤
      logFlatActiveWindow tStar h := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hx)) ht.le

end InfiniteZero
