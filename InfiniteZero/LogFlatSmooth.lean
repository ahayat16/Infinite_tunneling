import InfiniteZero.LogFlat
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Smoothness and vanishing derivatives of all weighted log-flat profiles -/

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace InfiniteZero

def weightedLogFlat (β tStar : ℝ) (k : ℕ) (P : Polynomial ℝ) (t : ℝ) : ℝ :=
  (t ^ k)⁻¹ * P.eval (Real.log (tStar / t)) * logFlat β tStar t

def nextLogFlatPolynomial (β : ℝ) (k : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.C (2 * β) * Polynomial.X - Polynomial.C (k : ℝ)) * P - P.derivative

@[simp] theorem weightedLogFlat_zero (β tStar : ℝ) (k : ℕ) (P : Polynomial ℝ) :
    weightedLogFlat β tStar k P 0 = 0 := by simp [weightedLogFlat, logFlat]

theorem weightedLogFlat_of_nonpos (β tStar : ℝ) (k : ℕ) (P : Polynomial ℝ)
    {t : ℝ} (ht : t ≤ 0) : weightedLogFlat β tStar k P t = 0 := by
  simp [weightedLogFlat, logFlat_of_nonpos β tStar ht]

private theorem tendsto_logFlat_logpow {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k N : ℕ) :
    Tendsto (fun t : ℝ => (t ^ k)⁻¹ * Real.log (tStar / t) ^ N * logFlat β tStar t)
      (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_quadratic hβ (k : ℝ) N).comp
    (tendsto_log_tStar_div_nhdsGT_zero hStar)).const_mul ((tStar ^ k)⁻¹)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  rw [logFlat_of_pos β tStar htpos]
  dsimp only [Function.comp_apply]
  have hp : (t ^ k)⁻¹ = (tStar ^ k)⁻¹ * Real.exp ((k : ℝ) * Real.log (tStar / t)) := by
    rw [Real.exp_nat_mul, Real.exp_log (div_pos hStar htpos), div_pow]
    field_simp [ne_of_gt hStar, ne_of_gt htpos]
  rw [hp, Real.exp_add]
  ring

theorem tendsto_weightedLogFlat_nhdsGT_zero {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) :
    Tendsto (weightedLogFlat β tStar k P) (𝓝[>] 0) (𝓝 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      · ext t
        simp only [weightedLogFlat, Polynomial.eval_add]
        ring
      · simp
  | monomial n a =>
      have h := (tendsto_logFlat_logpow hβ hStar k n).const_mul a
      rw [mul_zero] at h
      convert h using 1
      ext t
      simp only [weightedLogFlat, Polynomial.eval_monomial]
      ring

theorem tendsto_weightedLogFlat_zero {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) :
    Tendsto (weightedLogFlat β tStar k P) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (weightedLogFlat β tStar k P) 0 := by
    apply continuousAt_iff_continuous_left'_right'.2
    constructor
    · change Tendsto _ (𝓝[<] 0) (𝓝 (weightedLogFlat β tStar k P 0))
      rw [weightedLogFlat_zero]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (weightedLogFlat_of_nonpos β tStar k P (le_of_lt ht)).symm
    · change Tendsto _ (𝓝[>] 0) (𝓝 (weightedLogFlat β tStar k P 0))
      rw [weightedLogFlat_zero]
      exact tendsto_weightedLogFlat_nhdsGT_zero hβ hStar k P
  simpa only [weightedLogFlat_zero] using hc.tendsto

theorem weightedLogFlat_isLittleO_pow {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) (N : ℕ) :
    weightedLogFlat β tStar k P =o[𝓝 0] (fun t : ℝ => t ^ N) := by
  have hzero (t : ℝ) (ht : t ^ N = 0) : weightedLogFlat β tStar k P t = 0 := by
    rw [eq_zero_of_pow_eq_zero ht, weightedLogFlat_zero]
  apply (isLittleO_iff_tendsto hzero).2
  convert tendsto_weightedLogFlat_zero hβ hStar (k + N) P using 1
  ext t
  simp only [weightedLogFlat, pow_add, mul_inv_rev, div_eq_mul_inv]
  ring

theorem hasDerivAt_weightedLogFlat_zero {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) :
    HasDerivAt (weightedLogFlat β tStar k P) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h := ((weightedLogFlat_isLittleO_pow hβ hStar k P 1).tendsto_div_nhds_zero).mono_left
    (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simpa only [weightedLogFlat_zero, zero_add, sub_zero, smul_eq_mul,
    pow_one, div_eq_mul_inv, mul_comm] using h

private theorem hasDerivAt_log_tStar_div {tStar t : ℝ} (hStar : 0 < tStar) (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (tStar / s)) (-t⁻¹) t := by
  have h := (hasDerivAt_const t (Real.log tStar)).sub (Real.hasDerivAt_log (ne_of_gt ht))
  simp only [zero_sub] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  exact Real.log_div (ne_of_gt hStar) (ne_of_gt hs)

private theorem hasDerivAt_inv_nat_pow {t : ℝ} (ht : t ≠ 0) (k : ℕ) :
    HasDerivAt (fun s : ℝ => (s ^ k)⁻¹) (-(k : ℝ) * (t ^ (k + 1))⁻¹) t := by
  have h := hasDerivAt_zpow (-(k : ℤ)) t (Or.inl ht)
  have hi : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
  simpa only [hi, zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] using h

theorem hasDerivAt_weightedLogFlat_pos {β tStar t : ℝ}
    (hStar : 0 < tStar) (ht : 0 < t) (k : ℕ) (P : Polynomial ℝ) :
    HasDerivAt (weightedLogFlat β tStar k P)
      (weightedLogFlat β tStar (k + 1) (nextLogFlatPolynomial β k P) t) t := by
  have hy := hasDerivAt_log_tStar_div hStar ht
  have hP := (P.hasDerivAt (Real.log (tStar / t))).comp t hy
  have he := ((hy.pow 2).const_mul (-β)).exp
  have hprod := ((hasDerivAt_inv_nat_pow (ne_of_gt ht) k).mul hP).mul he
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat] at hprod
  have hderiv :
      ((-(k : ℝ) * (t ^ (k + 1))⁻¹) * P.eval (Real.log (tStar / t)) +
        (t ^ k)⁻¹ * (P.derivative.eval (Real.log (tStar / t)) * -t⁻¹)) *
        Real.exp (-β * Real.log (tStar / t) ^ 2) +
      ((t ^ k)⁻¹ * P.eval (Real.log (tStar / t))) *
        (Real.exp (-β * Real.log (tStar / t) ^ 2) *
          (-β * (2 * Real.log (tStar / t) ^ (2 - 1) * -t⁻¹))) =
      weightedLogFlat β tStar (k + 1) (nextLogFlatPolynomial β k P) t := by
    simp only [weightedLogFlat, nextLogFlatPolynomial, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      logFlat_of_pos β tStar ht, pow_succ, mul_inv_rev]
    norm_num
    ring
  rw [hderiv] at hprod
  apply hprod.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  exact congrArg (fun z => (s ^ k)⁻¹ * P.eval (Real.log (tStar / s)) * z)
    (logFlat_of_pos β tStar hs)

theorem hasDerivAt_weightedLogFlat {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (weightedLogFlat β tStar k P)
      (weightedLogFlat β tStar (k + 1) (nextLogFlatPolynomial β k P) t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [weightedLogFlat_of_nonpos β tStar (k + 1) _ ht.le]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ht] with s hs
    exact weightedLogFlat_of_nonpos β tStar k P hs.le
  · rw [weightedLogFlat_zero]
    exact hasDerivAt_weightedLogFlat_zero hβ hStar k P
  · exact hasDerivAt_weightedLogFlat_pos hStar ht k P

theorem deriv_weightedLogFlat {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) :
    deriv (weightedLogFlat β tStar k P) =
      weightedLogFlat β tStar (k + 1) (nextLogFlatPolynomial β k P) := by
  funext t
  exact (hasDerivAt_weightedLogFlat hβ hStar k P t).deriv

theorem contDiff_weightedLogFlat_nat {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (n k : ℕ) (P : Polynomial ℝ) :
    ContDiff ℝ n (weightedLogFlat β tStar k P) := by
  induction n generalizing k P with
  | zero =>
      change ContDiff ℝ 0 (weightedLogFlat β tStar k P)
      rw [contDiff_zero]
      exact continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_weightedLogFlat hβ hStar k P t).continuousAt
  | succ n ih =>
      rw [show (↑(n + 1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
      refine ⟨fun t => (hasDerivAt_weightedLogFlat hβ hStar k P t).differentiableAt, ?_, ?_⟩
      · intro h
        simp at h
      · rw [deriv_weightedLogFlat hβ hStar]
        exact ih _ _

/-- Every derivative stays in the same rapidly vanishing family; therefore
the zero extension is smooth to every order. -/
theorem contDiff_weightedLogFlat {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) :
    ContDiff ℝ ∞ (weightedLogFlat β tStar k P) := by
  apply contDiff_iff_forall_nat_le.2
  intro n _
  exact contDiff_weightedLogFlat_nat hβ hStar n k P

theorem contDiff_logFlat {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar) :
    ContDiff ℝ ∞ (logFlat β tStar) := by
  have heq : weightedLogFlat β tStar 0 (1 : Polynomial ℝ) = logFlat β tStar := by
    funext t
    simp [weightedLogFlat]
  rw [← heq]
  exact contDiff_weightedLogFlat hβ hStar 0 1

@[simp] theorem deriv_weightedLogFlat_zero {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ) :
    deriv (weightedLogFlat β tStar k P) 0 = 0 :=
  (hasDerivAt_weightedLogFlat_zero hβ hStar k P).deriv

/-- Every iterated derivative vanishes at the tip, not just the first one. -/
theorem iteratedDeriv_weightedLogFlat_zero {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (n k : ℕ) (P : Polynomial ℝ) :
    iteratedDeriv n (weightedLogFlat β tStar k P) 0 = 0 := by
  induction n generalizing k P with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ', deriv_weightedLogFlat hβ hStar]
      exact ih _ _

/-- The rapid-decay estimate is inherited by all derivatives. -/
theorem iteratedDeriv_weightedLogFlat_isLittleO_pow {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (n k : ℕ) (P : Polynomial ℝ) (N : ℕ) :
    iteratedDeriv n (weightedLogFlat β tStar k P) =o[𝓝 0] (fun t : ℝ => t ^ N) := by
  induction n generalizing k P with
  | zero => simpa using weightedLogFlat_isLittleO_pow hβ hStar k P N
  | succ n ih =>
      rw [iteratedDeriv_succ', deriv_weightedLogFlat hβ hStar]
      exact ih _ _

end InfiniteZero
