import InfiniteZero.ComplexLogFlatPhaseGrowth
import InfiniteZero.ComplexLogFlatCutoffAsymptotic

/-!
# Exact complex normalization of the Gaussian saddle leading term

The normalizer cancels the complex critical value, including its phase.
The identities retain the original scalar parameters and make no choice
of a logarithm of the leading term.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero

theorem logFlatSaddleNormalizer_mul_leading
    {β k tStar h : ℝ} {c : ℂ} (hβ : 0 < β)
    (hr : 0 < (logFlatSaddleRoot β k tStar c h).re) :
    logFlatSaddleNormalizer β k tStar c h * logFlatSaddleLeading β k tStar c h =
      ((tStar ^ (k + 1) * Real.sqrt (Real.pi / β) : ℝ) : ℂ) := by
  let r := (logFlatSaddleRoot β k tStar c h).re
  have hs : Real.sqrt r * Real.sqrt (Real.pi / (β * r)) =
      Real.sqrt (Real.pi / β) := by
    rw [← Real.sqrt_mul hr.le]
    congr 1
    dsimp [r]
    field_simp
  change ((Real.sqrt r : ℂ) * Complex.exp (logFlatSaddleValue β k tStar c h)) *
      (((tStar ^ (k + 1) * Real.sqrt (Real.pi / (β * r)) : ℝ) : ℂ) *
        Complex.exp (-logFlatSaddleValue β k tStar c h)) = _
  calc
    _ = ((tStar ^ (k + 1) *
        (Real.sqrt r * Real.sqrt (Real.pi / (β * r))) : ℝ) : ℂ) *
        (Complex.exp (logFlatSaddleValue β k tStar c h) *
          Complex.exp (-logFlatSaddleValue β k tStar c h)) := by push_cast; ring
    _ = _ := by rw [hs, ← Complex.exp_add]; simp

theorem logFlatSaddleNormalizer_sq_mul_leading_sq_two
    {β tStar h : ℝ} {c : ℂ} (hβ : 0 < β)
    (hr : 0 < (logFlatSaddleRoot β 2 tStar c h).re) :
    logFlatSaddleNormalizer β 2 tStar c h ^ 2 *
      logFlatSaddleLeading β 2 tStar c h ^ 2 =
        (tStar : ℂ) ^ 6 * (Real.pi / β : ℂ) := by
  calc
    _ = (logFlatSaddleNormalizer β 2 tStar c h *
        logFlatSaddleLeading β 2 tStar c h) ^ 2 := by ring
    _ = (((tStar ^ ((2 : ℝ) + 1) * Real.sqrt (Real.pi / β) : ℝ) : ℂ)) ^ 2 := by
      rw [logFlatSaddleNormalizer_mul_leading hβ hr]
    _ = _ := by
      rw [show (2 : ℝ) + 1 = (3 : ℕ) by norm_num, Real.rpow_natCast]
      rw [← Complex.ofReal_pow, mul_pow, Real.sq_sqrt (div_pos Real.pi_pos hβ).le]
      push_cast
      ring

theorem logFlatSaddleNormalizer_ne_zero
    {β k tStar h : ℝ} {c : ℂ}
    (hr : 0 < (logFlatSaddleRoot β k tStar c h).re) :
    logFlatSaddleNormalizer β k tStar c h ≠ 0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne')
    (Complex.exp_ne_zero _)

theorem logFlatSaddleLeading_ne_zero
    {β k tStar h : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hr : 0 < (logFlatSaddleRoot β k tStar c h).re) :
    logFlatSaddleLeading β k tStar c h ≠ 0 := by
  have hpos : 0 < tStar ^ (k + 1) * Real.sqrt (Real.pi / β) := by positivity
  have hprod := logFlatSaddleNormalizer_mul_leading hβ hr
  exact (mul_ne_zero_iff.mp (hprod ▸ Complex.ofReal_ne_zero.mpr hpos.ne')).2

theorem eventually_logFlatSaddleNormalizer_leading_ne_zero
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      logFlatSaddleNormalizer β k tStar c h ≠ 0 ∧
        logFlatSaddleLeading β k tStar c h ≠ 0 := by
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc]
    with h hw
  have hr : 0 < (logFlatSaddleRoot β k tStar c h).re := by linarith [hw.1]
  exact ⟨logFlatSaddleNormalizer_ne_zero hr, logFlatSaddleLeading_ne_zero hβ ht hr⟩

theorem eventually_logFlatSaddleNormalizer_sq_mul_leading_sq_two
    {β tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      logFlatSaddleNormalizer β 2 tStar c h ^ 2 *
        logFlatSaddleLeading β 2 tStar c h ^ 2 =
          (tStar : ℂ) ^ 6 * (Real.pi / β : ℂ) := by
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := (2 : ℝ)) hβ.ne' ht.ne' hc]
    with h hw
  exact logFlatSaddleNormalizer_sq_mul_leading_sq_two hβ (by linarith [hw.1])

end InfiniteZero
