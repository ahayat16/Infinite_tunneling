import InfiniteZero.SaddleNormalizationIdentity
import InfiniteZero.SaddleEnvelopeComparison

/-!
# The sharp quadratic logarithmic cost of the positive saddle size

The logarithmic saddle equation gives Re w ≤ log(1/h) + O(1).
The exact critical value then has real part at most
β (log(1/h) + O(1))², retaining the coefficient β needed to exclude
scattered sources. All scalar parameters precede h → 0+.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

theorem eventually_re_logFlatSaddleRoot_le_log_add
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (logFlatSaddleRoot β k tStar c h).re ≤ Real.log (1 / h) +
        ‖logFlatLambertDisplacement β k tStar c‖ := by
  filter_upwards [eventually_logFlatSaddleRoot_log_eq β k tStar c,
    eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc] with h he hw
  have hn : 1 ≤ ‖logFlatSaddleRoot β k tStar c h‖ := by
    linarith [hw.1, Complex.re_le_norm (logFlatSaddleRoot β k tStar c h)]
  have hlog := Real.log_nonneg hn
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.log_re] at hre
  linarith [Complex.re_le_norm (logFlatLambertDisplacement β k tStar c)]

theorem eventually_re_logFlatSaddleValue_le_sharp
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (logFlatSaddleValue β k tStar c h).re ≤
        β * (Real.log (1 / h) + ‖logFlatLambertDisplacement β k tStar c‖ + 1) ^ 2 := by
  filter_upwards [eventually_re_logFlatSaddleRoot_le_log_add (k := k) hβ ht hc,
    eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc,
    eventually_logFlatSaddleRoot_value_hessian (k := k) hβ.ne' ht.ne' hc]
    with h hr hw hv
  have hsq : ((logFlatSaddleRoot β k tStar c h).re + 1) ^ 2 ≤
      (Real.log (1 / h) + ‖logFlatLambertDisplacement β k tStar c‖ + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith [hw.1]) (by linarith) 2
  have hm := mul_le_mul_of_nonneg_left hsq hβ.le
  have hi : 0 ≤ β * (logFlatSaddleRoot β k tStar c h).im ^ 2 := by positivity
  have hcoef : 0 ≤ (k + 1) ^ 2 / (4 * β) := by positivity
  unfold logFlatSaddleValue
  rw [hv.1]
  simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  simp only [pow_two] at hm hi hcoef
  nlinarith only [hm, hi, hcoef, hβ]

/-- The reciprocal square has one Gaussian factor Re w and the exponential
of twice the real critical value. This identity contains no asymptotic loss. -/
theorem inv_logFlatSaddleLeadingSize_sq_eq
    {β k tStar h : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hr : 0 < (logFlatSaddleRoot β k tStar c h).re) :
    (logFlatSaddleLeadingSize β k tStar c h)⁻¹ ^ 2 =
      (logFlatSaddleRoot β k tStar c h).re *
        Real.exp (2 * (logFlatSaddleValue β k tStar c h).re) /
        (tStar ^ (k + 1) * Real.sqrt (Real.pi / β)) ^ 2 := by
  let S := logFlatSaddleLeadingSize β k tStar c h
  let B := tStar ^ (k + 1) * Real.sqrt (Real.pi / β)
  have hS : 0 < S := by dsimp [S, logFlatSaddleLeadingSize]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hid : ‖logFlatSaddleNormalizer β k tStar c h‖ * S = B :=
    norm_logFlatSaddleNormalizer_mul_leadingSize hβ hr
  have hinv : S⁻¹ = ‖logFlatSaddleNormalizer β k tStar c h‖ / B := by
    apply (eq_div_iff hB.ne').mpr
    rw [← hid]
    field_simp
  have hn : ‖logFlatSaddleNormalizer β k tStar c h‖ ^ 2 =
      (logFlatSaddleRoot β k tStar c h).re *
        Real.exp (2 * (logFlatSaddleValue β k tStar c h).re) := by
    simp only [logFlatSaddleNormalizer, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp, mul_pow,
      Real.sq_sqrt hr.le, logFlatSaddleValue]
    rw [two_mul, Real.exp_add, pow_two]
  change S⁻¹ ^ 2 = _
  rw [hinv, div_pow, hn]

/-- Any strictly positive quadratic-logarithmic margin absorbs the exact
reciprocal saddle size and every fixed semiclassical polynomial loss. -/
theorem tendsto_inv_saddleLeadingSize_sq_polynomial_log_exp
    {β k tStar η : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (hη : 0 < η) (N : ℕ) :
    Tendsto (fun h : ℝ => (logFlatSaddleLeadingSize β k tStar c h)⁻¹ ^ 2 *
      (h ^ N)⁻¹ * Real.exp (-(2 * β + η) * (Real.log (1 / h)) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  let D := ‖logFlatLambertDisplacement β k tStar c‖ + 1
  let B := tStar ^ (k + 1) * Real.sqrt (Real.pi / β)
  let A := 4 * β * D + (N : ℝ)
  let K := (2 / B ^ 2) * Real.exp (2 * β * D ^ 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hlim := ((tendsto_pow_mul_exp_quadratic hη A 1).comp hlog).const_mul K
  simp only [Function.comp_def, pow_one, mul_zero] at hlim
  apply squeeze_zero'
    (g := fun h : ℝ => K * (Real.log (1 / h) *
      Real.exp (-η * (Real.log (1 / h)) ^ 2 + A * Real.log (1 / h)))) ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hhpos : 0 < h := hh
    positivity
  · filter_upwards [self_mem_nhdsWithin,
      eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc,
      eventually_norm_logFlatSaddleRoot_le β k tStar c,
      eventually_re_logFlatSaddleValue_le_sharp (k := k) hβ ht hc]
      with h hh hw hn hv
    have hhpos : 0 < h := hh
    have hr : 0 < (logFlatSaddleRoot β k tStar c h).re := by linarith [hw.1]
    let ℓ := Real.log (1 / h)
    have hre : (logFlatSaddleRoot β k tStar c h).re ≤ 2 * ℓ :=
      (Complex.re_le_norm _).trans hn
    have hℓ : 0 ≤ ℓ := by linarith
    have hvalue : (logFlatSaddleValue β k tStar c h).re ≤ β * (ℓ + D) ^ 2 := by
      simpa only [ℓ, D, add_assoc] using hv
    have hexp : Real.exp (2 * (logFlatSaddleValue β k tStar c h).re) ≤
        Real.exp (2 * β * (ℓ + D) ^ 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hnum := mul_le_mul hre hexp (Real.exp_pos _).le (by positivity : 0 ≤ 2 * ℓ)
    have hbase := div_le_div_of_nonneg_right hnum (sq_nonneg B)
    have hp : (h ^ N)⁻¹ = Real.exp ((N : ℝ) * ℓ) := by
      rw [Real.exp_nat_mul, Real.exp_log (one_div_pos.mpr hhpos)]
      simp only [one_div, inv_pow]
    rw [inv_logFlatSaddleLeadingSize_sq_eq hβ ht hr, hp]
    change ((logFlatSaddleRoot β k tStar c h).re *
      Real.exp (2 * (logFlatSaddleValue β k tStar c h).re) / B ^ 2) *
      Real.exp ((N : ℝ) * ℓ) * Real.exp (-(2 * β + η) * ℓ ^ 2) ≤
        K * (ℓ * Real.exp (-η * ℓ ^ 2 + A * ℓ))
    calc
      _ ≤ (2 * ℓ * Real.exp (2 * β * (ℓ + D) ^ 2) / B ^ 2) *
          Real.exp ((N : ℝ) * ℓ) * Real.exp (-(2 * β + η) * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = (2 / B ^ 2) * ℓ *
          (Real.exp (2 * β * (ℓ + D) ^ 2) * Real.exp ((N : ℝ) * ℓ) *
            Real.exp (-(2 * β + η) * ℓ ^ 2)) := by ring
      _ = (2 / B ^ 2) * ℓ *
          (Real.exp (2 * β * D ^ 2) * Real.exp (-η * ℓ ^ 2 + A * ℓ)) := by
        congr 1
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [A]
        ring
      _ = _ := by dsimp [K]; ring

/-- The sharp reciprocal-size upper bound, including an arbitrary fixed
power of h⁻¹. All parameters precede the small-h threshold. -/
theorem eventually_inv_saddleLeadingSize_sq_polynomial_le_exp
    {β k tStar η : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (hη : 0 < η) (N : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (logFlatSaddleLeadingSize β k tStar c h)⁻¹ ^ 2 * (h ^ N)⁻¹ ≤
        Real.exp ((2 * β + η) * (Real.log (1 / h)) ^ 2) := by
  filter_upwards [(tendsto_inv_saddleLeadingSize_sq_polynomial_log_exp
    (k := k) hβ ht hc hη N).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with h hh
  have hbound := mul_le_mul_of_nonneg_right hh.le
    (Real.exp_pos ((2 * β + η) * (Real.log (1 / h)) ^ 2)).le
  simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero,
    mul_one, one_mul] using hbound

/-- Half of a prescribed strict logarithmic margin can be retained as an
explicit decaying upper bound after saddle normalization. -/
theorem eventually_inv_saddleLeadingSize_sq_polynomial_log_exp_le
    {β k tStar η : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (hη : 0 < η) (N : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (logFlatSaddleLeadingSize β k tStar c h)⁻¹ ^ 2 * (h ^ N)⁻¹ *
        Real.exp (-(2 * β + η) * (Real.log (1 / h)) ^ 2) ≤
          Real.exp (-(η / 2) * (Real.log (1 / h)) ^ 2) := by
  filter_upwards [eventually_inv_saddleLeadingSize_sq_polynomial_le_exp
    (k := k) hβ ht hc (half_pos hη) N] with h hh
  calc
    _ ≤ Real.exp ((2 * β + η / 2) * (Real.log (1 / h)) ^ 2) *
        Real.exp (-(2 * β + η) * (Real.log (1 / h)) ^ 2) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

end InfiniteZero
