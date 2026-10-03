import InfiniteZero.ComplexLogFlatLeading
import InfiniteZero.ComplexLogFlatContour
import InfiniteZero.ComplexLogFlatChange
import InfiniteZero.ComplexLogFlatErrors
import InfiniteZero.ComplexLogFlatNormalization

/-! Assembly of the log-flat normal integral, including its original contour. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

theorem logFlatComplex_ray_shift_full {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) (a v : ℝ)
    (hi : Integrable (fun x : ℝ =>
      logFlatComplexIntegrand β k C ((x : ℂ) + (v : ℂ) * Complex.I))) :
    (∫ x in Ioi a, logFlatComplexIntegrand β k C (x : ℂ)) =
      (∫ x : ℝ, logFlatComplexIntegrand β k C ((x : ℂ) + (v : ℂ) * Complex.I)) +
        (Complex.I * (∫ η in 0..v,
          logFlatComplexIntegrand β k C ((a : ℂ) + (η : ℂ) * Complex.I)) -
          ∫ x in Iic a, logFlatComplexIntegrand β k C ((x : ℂ) + (v : ℂ) * Complex.I)) := by
  have hr := logFlatComplex_ray_shift hβ k C a v
  have hsplit := integral_add_compl (s := Iic a) measurableSet_Iic hi
  simp only [compl_Iic] at hsplit
  linear_combination hr + hsplit

theorem integral_logFlatComplex_saddleLine (β k : ℝ) (C w : ℂ) :
    (∫ x : ℝ, logFlatComplexIntegrand β k C ((x : ℂ) + (w.im : ℂ) * Complex.I)) =
      ∫ q : ℝ, Complex.exp (-logFlatComplexPhase β k C
        (logFlatComplexCritical β k w + (q : ℂ))) := by
  have he (q : ℝ) : logFlatComplexCritical β k w + (q : ℂ) =
      ((q + (logFlatComplexCritical β k w).re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
    have him : (logFlatComplexCritical β k w).im = w.im := by
      simp only [logFlatComplexCritical, Complex.sub_im, Complex.ofReal_im, sub_zero]
    apply Complex.ext <;> simp [him, Complex.mul_re, Complex.mul_im, add_comm]
  simp_rw [he]
  exact (integral_add_right_eq_self
    (fun x : ℝ => logFlatComplexIntegrand β k C ((x : ℂ) + (w.im : ℂ) * Complex.I))
    (logFlatComplexCritical β k w).re).symm

def logFlatRayError (β k tStar : ℝ) (c : ℂ) (a h : ℝ) : ℂ :=
  Complex.I * (∫ η in 0..(logFlatSaddleRoot β k tStar c h).im,
    logFlatComplexIntegrand β k (c * (tStar : ℂ) / (h : ℂ))
      ((a : ℂ) + (η : ℂ) * Complex.I)) -
  ∫ x in Iic a, logFlatComplexIntegrand β k (c * (tStar : ℂ) / (h : ℂ))
    ((x : ℂ) + ((logFlatSaddleRoot β k tStar c h).im : ℂ) * Complex.I)

theorem logFlatComplex_ray_eq_saddle_add_error {β : ℝ} (hβ : 0 < β)
    (k tStar : ℝ) (c : ℂ) (a h : ℝ)
    (hi : Integrable (fun x : ℝ => logFlatComplexIntegrand β k (c * (tStar : ℂ) / (h : ℂ))
      ((x : ℂ) + ((logFlatSaddleRoot β k tStar c h).im : ℂ) * Complex.I))) :
    (∫ x in Ioi a, logFlatComplexIntegrand β k (c * (tStar : ℂ) / (h : ℂ)) (x : ℂ)) =
      logFlatSaddleHorizontalIntegral β k tStar c h + logFlatRayError β k tStar c a h := by
  rw [logFlatComplex_ray_shift_full hβ k _ a _ hi, integral_logFlatComplex_saddleLine]
  rfl

theorem eventually_logFlatRayError_bound {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) (a : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖logFlatRayError β k tStar c a h‖ ≤
        ((Real.pi + Real.sqrt (Real.pi / (β / 2))) * logFlatErrorMajorant β k) *
          Real.exp (-logFlatContourErrorRate tStar c a / h) := by
  filter_upwards [eventually_logFlatContour_errors_le (k := k) hβ ht hc a] with h hs
  unfold logFlatRayError
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul]
  exact hs.2

theorem eventually_logFlatRay_eq_saddle_add_error {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) (a : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ x in Ioi a, logFlatComplexIntegrand β k (c * (tStar : ℂ) / (h : ℂ)) (x : ℂ)) =
        logFlatSaddleHorizontalIntegral β k tStar c h + logFlatRayError β k tStar c a h := by
  filter_upwards [eventually_logFlatContour_errors_le (k := k) hβ ht hc a] with h hs
  exact logFlatComplex_ray_eq_saddle_add_error hβ k tStar c a h hs.1

theorem tendsto_logFlatRay_normalized {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) (a : ℝ) :
    Tendsto (fun h : ℝ => (Real.sqrt (logFlatSaddleRoot β k tStar c h).re : ℂ) *
      Complex.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))) *
      (∫ x in Ioi a, logFlatComplexIntegrand β k (c * (tStar : ℂ) / (h : ℂ)) (x : ℂ)))
        (𝓝[>] 0) (𝓝 ((Real.sqrt (Real.pi / β) : ℝ) : ℂ)) := by
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  have herror := tendsto_logFlatSaddle_normalized_remainder (k := k) hβ ht hcne
    (logFlatContourErrorRate_pos ht hc a) (eventually_logFlatRayError_bound (k := k) hβ ht hc a)
  have hsum := (tendsto_logFlatSaddle_horizontal_leading (k := k) hβ ht hcne).add herror
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_logFlatRay_eq_saddle_add_error (k := k) hβ ht hc a] with h he
  rw [he, mul_add]

/-- The genuine leading asymptotic of the original complex normal integral.
All parameters are fixed before `h → 0+`; the Jacobian power is retained. -/
theorem tendsto_complexLogFlatIntegral_normalized {β tStar t₂ : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (ht₂ : 0 < t₂) (hc : 0 < c.re) (m : ℕ) :
    Tendsto (fun h : ℝ => (Real.sqrt (logFlatSaddleRoot β (m : ℝ) tStar c h).re : ℂ) *
      Complex.exp (logFlatComplexPhase β (m : ℝ) (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β (m : ℝ) (logFlatSaddleRoot β (m : ℝ) tStar c h))) *
      (∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t)) (𝓝[>] 0)
        (𝓝 ((tStar : ℂ) ^ (m + 1) * ((Real.sqrt (Real.pi / β) : ℝ) : ℂ))) := by
  have hlim := (tendsto_logFlatRay_normalized (k := (m : ℝ)) hβ ht hc
    (Real.log (tStar / t₂))).const_mul ((tStar : ℂ) ^ (m + 1))
  apply hlim.congr
  intro h
  rw [integral_complexLogFlat_logarithmic_change ht ht₂]
  dsimp only [logFlatComplexIntegrand]
  ring

theorem eventually_complexLogFlatIntegral_ne_zero {β tStar t₂ : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (ht₂ : 0 < t₂) (hc : 0 < c.re) (m : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t) ≠ 0 := by
  have hnonzero : (tStar : ℂ) ^ (m + 1) * ((Real.sqrt (Real.pi / β) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne'))
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hβ)).ne')
  filter_upwards [(tendsto_complexLogFlatIntegral_normalized hβ ht ht₂ hc m).eventually_ne hnonzero]
    with h hh
  intro he
  exact hh (by rw [he, mul_zero])

end InfiniteZero
