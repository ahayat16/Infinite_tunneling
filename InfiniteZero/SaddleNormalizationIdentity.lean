import InfiniteZero.ComplexLogFlatPhaseGrowth
import InfiniteZero.LogFlatPolynomialErrors

/-!
# Reciprocal bounds for the actual positive scalar saddle envelope

The leading size is the one already used in the proved amplitude-phase
decomposition. Its reciprocal is identified with the norm of the existing
saddle normalizer. A strict action reserve therefore absorbs its square
and every fixed polynomial loss. This does not assert any active-cell
asymptotic.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero

theorem norm_logFlatSaddleNormalizer_mul_leadingSize
    {β k tStar h : ℝ} {c : ℂ} (hβ : 0 < β)
    (hr : 0 < (logFlatSaddleRoot β k tStar c h).re) :
    ‖logFlatSaddleNormalizer β k tStar c h‖ *
      logFlatSaddleLeadingSize β k tStar c h =
        tStar ^ (k + 1) * Real.sqrt (Real.pi / β) := by
  let r := (logFlatSaddleRoot β k tStar c h).re
  have hs : Real.sqrt r * Real.sqrt (Real.pi / (β * r)) =
      Real.sqrt (Real.pi / β) := by
    rw [← Real.sqrt_mul hr.le]
    congr 1
    dsimp [r]
    field_simp
  simp only [logFlatSaddleNormalizer, logFlatSaddleLeadingSize, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_exp, logFlatSaddleValue]
  rw [show Real.sqrt (logFlatSaddleRoot β k tStar c h).re *
      Real.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))).re *
      (tStar ^ (k + 1) * Real.sqrt (Real.pi /
        (β * (logFlatSaddleRoot β k tStar c h).re)) *
        Real.exp (-(logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
          (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))).re)) =
      tStar ^ (k + 1) * (Real.sqrt r * Real.sqrt (Real.pi / (β * r))) *
        (Real.exp (logFlatSaddleValue β k tStar c h).re *
          Real.exp (-(logFlatSaddleValue β k tStar c h).re)) by
      dsimp [r, logFlatSaddleValue]; ring]
  rw [hs, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem tendsto_inv_saddleLeadingSize_sq_polynomial_exp
    {β k tStar d : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (hd : 0 < d) (N : ℕ) :
    Tendsto (fun h : ℝ => (logFlatSaddleLeadingSize β k tStar c h)⁻¹ ^ 2 *
      (h ^ N)⁻¹ * Real.exp (-d / h)) (𝓝[>] 0) (𝓝 0) := by
  let B := tStar ^ (k + 1) * Real.sqrt (Real.pi / β)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlim := (tendsto_logFlatSaddleProduct_normalized_polynomial_stretched_error
    (k := k) hβ ht hc hc hd (by norm_num : (0 : ℝ) < 1) N).div_const (B ^ 2)
  simp only [zero_div] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc,
    eventually_logFlatSaddleLeadingSize_pos (k := k) hβ ht hc] with h hh hw hs
  have hhpos : 0 < h := hh
  have hr : 0 < (logFlatSaddleRoot β k tStar c h).re := by linarith [hw.1]
  have hid := norm_logFlatSaddleNormalizer_mul_leadingSize hβ hr
  have hinv : (logFlatSaddleLeadingSize β k tStar c h)⁻¹ =
      ‖logFlatSaddleNormalizer β k tStar c h‖ / B := by
    apply (eq_div_iff hB.ne').mpr
    change ‖logFlatSaddleNormalizer β k tStar c h‖ *
      logFlatSaddleLeadingSize β k tStar c h = B at hid
    rw [← hid]
    field_simp
  rw [hinv, norm_mul, one_mul, Real.exp_log (one_div_pos.mpr hhpos)]
  simp only [div_pow, mul_one_div]
  ring

/-- An explicit exponential bound, retaining half the strict action reserve.
The scalar saddle parameters are fixed before the small-h threshold. -/
theorem eventually_inv_saddleLeadingSize_sq_polynomial_exp_le
    {β k tStar a : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (ha : 0 < a) (N : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (logFlatSaddleLeadingSize β k tStar c h)⁻¹ ^ 2 *
        (h ^ N)⁻¹ * Real.exp (-a / h) ≤ Real.exp (-(a / 2) / h) := by
  have hlim := tendsto_inv_saddleLeadingSize_sq_polynomial_exp
    (k := k) hβ ht hc (half_pos ha) N
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with h hh
  have he : Real.exp (-a / h) =
      Real.exp (-(a / 2) / h) * Real.exp (-(a / 2) / h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hh.le (Real.exp_pos (-(a / 2) / h)).le

end InfiniteZero
