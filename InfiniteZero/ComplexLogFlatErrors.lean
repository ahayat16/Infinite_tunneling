import InfiniteZero.ComplexSaddleBranches
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exponentially small discarded pieces of the complex log-flat contour

Both estimates concern their actual Lebesgue integrals. The angular control
comes from the constructed saddle; the remaining argument is a Gaussian
majorant and the positive real part of the original coefficient.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def logFlatContourFunction (β k tStar : ℝ) (c : ℂ) (h : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ)) z)

def logFlatErrorMajorant (β k : ℝ) : ℝ :=
  Real.exp (β * Real.pi ^ 2 + (k + 1) ^ 2 / (2 * β))

def logFlatContourErrorRate (tStar : ℝ) (c : ℂ) (y₂ : ℝ) : ℝ :=
  tStar * Real.exp (-y₂) * c.re

theorem logFlatContourErrorRate_pos {tStar : ℝ} {c : ℂ}
    (ht : 0 < tStar) (hc : 0 < c.re) (y₂ : ℝ) :
    0 < logFlatContourErrorRate tStar c y₂ := by
  exact mul_pos (mul_pos ht (Real.exp_pos _)) hc

theorem norm_logFlatContourFunction_horizontal (β k tStar h x η : ℝ) (c : ℂ) :
    ‖logFlatContourFunction β k tStar c h ((x : ℂ) + (η : ℂ) * Complex.I)‖ =
      Real.exp (-β * x ^ 2 + β * η ^ 2 - (k + 1) * x -
        (tStar / h * Real.exp (-x)) * (c * Complex.exp (-(η : ℂ) * Complex.I)).re) := by
  have he : (c * (tStar : ℂ) / (h : ℂ)) *
      Complex.exp (-((x : ℂ) + (η : ℂ) * Complex.I)) =
      ((tStar / h * Real.exp (-x) : ℝ) : ℂ) *
        (c * Complex.exp (-(η : ℂ) * Complex.I)) := by
    rw [neg_add, Complex.exp_add]
    push_cast
    ring_nf
  rw [logFlatContourFunction, Complex.norm_exp, Complex.neg_re, logFlatComplexPhase, he]
  congr 1
  simp [Complex.add_re, Complex.mul_re, pow_two, Complex.mul_im,
    Complex.exp_re, Complex.exp_im]
  ring_nf

private theorem quadratic_linear_upper {β : ℝ} (hβ : 0 < β) (k x : ℝ) :
    -β * x ^ 2 - (k + 1) * x ≤
      -(β / 2) * x ^ 2 + (k + 1) ^ 2 / (2 * β) := by
  have he : (k + 1) ^ 2 / (2 * β) * (2 * β) = (k + 1) ^ 2 := by
    field_simp
  nlinarith [sq_nonneg (β * x + (k + 1))]

private theorem vertical_quadratic_le {η : ℝ} (hη : |η| ≤ Real.pi) : η ^ 2 ≤ Real.pi ^ 2 := by
  have h := abs_le.mp hη
  nlinarith [sq_nonneg (η - Real.pi), sq_nonneg (η + Real.pi)]

/-- A full horizontal line is dominated by a fixed Gaussian. -/
theorem norm_logFlatContourFunction_le_gaussian {β tStar h η : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 ≤ tStar) (hh : 0 < h) (hη : |η| ≤ Real.pi)
    (hc : 0 ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re) (k x : ℝ) :
    ‖logFlatContourFunction β k tStar c h ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      logFlatErrorMajorant β k * Real.exp (-(β / 2) * x ^ 2) := by
  rw [norm_logFlatContourFunction_horizontal, logFlatErrorMajorant, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := quadratic_linear_upper hβ k x
  have hv := mul_le_mul_of_nonneg_left (vertical_quadratic_le hη) hβ.le
  have hc' : 0 ≤ (tStar / h * Real.exp (-x)) *
      (c * Complex.exp (-(η : ℂ) * Complex.I)).re := by positivity
  linarith

theorem integrable_logFlatContourFunction_horizontal {β tStar h η : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 ≤ tStar) (hh : 0 < h) (hη : |η| ≤ Real.pi)
    (hc : 0 ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re) (k : ℝ) :
    Integrable (fun x : ℝ =>
      logFlatContourFunction β k tStar c h ((x : ℂ) + (η : ℂ) * Complex.I)) := by
  apply ((integrable_exp_neg_mul_sq (half_pos hβ)).const_mul
    (logFlatErrorMajorant β k)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold logFlatContourFunction logFlatComplexPhase
    fun_prop
  · exact Eventually.of_forall (norm_logFlatContourFunction_le_gaussian hβ ht hh hη hc k)

/-- Left of a fixed real endpoint, the Gaussian bound gains `exp (-d/h)`. -/
theorem norm_logFlatContourFunction_left_le {β tStar h η : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hh : 0 < h) (hη : |η| ≤ Real.pi)
    (hc : 0 < c.re) (hrot : c.re ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re)
    (k : ℝ) {x y₂ : ℝ} (hx : x ≤ y₂) :
    ‖logFlatContourFunction β k tStar c h ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      (logFlatErrorMajorant β k * Real.exp (-logFlatContourErrorRate tStar c y₂ / h)) *
        Real.exp (-(β / 2) * x ^ 2) := by
  have he : Real.exp (-y₂) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (neg_le_neg hx)
  have hcoeff : logFlatContourErrorRate tStar c y₂ / h ≤
      (tStar / h * Real.exp (-x)) * (c * Complex.exp (-(η : ℂ) * Complex.I)).re := by
    calc
      _ = (tStar / h * Real.exp (-y₂)) * c.re := by
        unfold logFlatContourErrorRate
        ring_nf
      _ ≤ (tStar / h * Real.exp (-x)) * c.re := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hrot (by positivity)
  rw [norm_logFlatContourFunction_horizontal, logFlatErrorMajorant,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [neg_div]
  have hs := quadratic_linear_upper hβ k x
  have hv := mul_le_mul_of_nonneg_left (vertical_quadratic_le hη) hβ.le
  linarith

/-- The actual discarded horizontal tail has an explicit Gaussian prefactor. -/
theorem norm_integral_logFlatContourFunction_left_le {β tStar h η : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hh : 0 < h) (hη : |η| ≤ Real.pi)
    (hc : 0 < c.re) (hrot : c.re ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re)
    (k y₂ : ℝ) :
    ‖∫ x in Iic y₂,
        logFlatContourFunction β k tStar c h ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      (logFlatErrorMajorant β k * Real.sqrt (Real.pi / (β / 2))) *
        Real.exp (-logFlatContourErrorRate tStar c y₂ / h) := by
  let K := logFlatErrorMajorant β k * Real.exp (-logFlatContourErrorRate tStar c y₂ / h)
  have hK : 0 ≤ K := by dsimp [K, logFlatErrorMajorant]; positivity
  have hi : Integrable (fun x : ℝ => K * Real.exp (-(β / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (half_pos hβ)).const_mul K
  calc
    _ ≤ ∫ x in Iic y₂, K * Real.exp (-(β / 2) * x ^ 2) := by
      apply norm_integral_le_of_norm_le hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact norm_logFlatContourFunction_left_le hβ ht hh hη hc hrot k hx
    _ ≤ ∫ x : ℝ, K * Real.exp (-(β / 2) * x ^ 2) :=
      setIntegral_le_integral hi (Eventually.of_forall fun x => by positivity)
    _ = _ := by
      rw [integral_const_mul, integral_gaussian]
      dsimp [K]
      ring_nf

/-- The fixed vertical connector has length at most `π`. -/
theorem norm_integral_logFlatContourFunction_connector_le {β tStar h v : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hh : 0 < h) (hv : |v| ≤ Real.pi)
    (hc : 0 < c.re)
    (hrot : ∀ η ∈ uIcc 0 v, c.re ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re)
    (k y₂ : ℝ) :
    ‖∫ η in (0 : ℝ)..v,
        logFlatContourFunction β k tStar c h ((y₂ : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      (Real.pi * logFlatErrorMajorant β k) *
        Real.exp (-logFlatContourErrorRate tStar c y₂ / h) := by
  let K := logFlatErrorMajorant β k * Real.exp (-logFlatContourErrorRate tStar c y₂ / h)
  have hK : 0 ≤ K := by dsimp [K, logFlatErrorMajorant]; positivity
  have hbound : ∀ η ∈ uIoc (0 : ℝ) v,
      ‖logFlatContourFunction β k tStar c h ((y₂ : ℂ) + (η : ℂ) * Complex.I)‖ ≤ K := by
    intro η hη
    have hη' : η ∈ uIcc 0 v := uIoc_subset_uIcc hη
    have hηabs : |η| ≤ Real.pi := by
      have hm : |η| ≤ |v| := by
        rcases le_total 0 v with hv0 | hv0
        · rw [uIcc_of_le hv0] at hη'
          rw [abs_of_nonneg hη'.1, abs_of_nonneg hv0]
          exact hη'.2
        · rw [uIcc_of_ge hv0] at hη'
          rw [abs_of_nonpos hη'.2, abs_of_nonpos hv0]
          exact neg_le_neg hη'.1
      exact hm.trans hv
    have hg := norm_logFlatContourFunction_left_le hβ ht hh hηabs hc (hrot η hη') k
      (x := y₂) (y₂ := y₂) le_rfl
    have hexp : Real.exp (-(β / 2) * y₂ ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg y₂]
    exact hg.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hK)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simp only [sub_zero] at hi
  calc
    _ ≤ K * |v| := hi
    _ ≤ K * Real.pi := mul_le_mul_of_nonneg_left hv hK
    _ = _ := by dsimp [K]; ring_nf

/-- For the constructed saddle both discarded pieces have a common positive
exponential rate and an explicit constant independent of `h`. -/
theorem eventually_logFlatContour_errors_le {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) (y₂ : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (fun x : ℝ => logFlatContourFunction β k tStar c h
        ((x : ℂ) + ((logFlatSaddleRoot β k tStar c h).im : ℂ) * Complex.I)) ∧
      ‖∫ η in (0 : ℝ)..(logFlatSaddleRoot β k tStar c h).im,
          logFlatContourFunction β k tStar c h ((y₂ : ℂ) + (η : ℂ) * Complex.I)‖ +
        ‖∫ x in Iic y₂, logFlatContourFunction β k tStar c h
          ((x : ℂ) + ((logFlatSaddleRoot β k tStar c h).im : ℂ) * Complex.I)‖ ≤
        ((Real.pi + Real.sqrt (Real.pi / (β / 2))) * logFlatErrorMajorant β k) *
          Real.exp (-logFlatContourErrorRate tStar c y₂ / h) := by
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  filter_upwards [eventually_logFlatSaddleRoot_connector_re (k := k) hβ ht hc,
    eventually_logFlatSaddleRoot_arg (k := k) hβ ht hcne, self_mem_nhdsWithin]
    with h hrot harg hh
  have hhpos : 0 < h := hh
  have hv : |(logFlatSaddleRoot β k tStar c h).im| ≤ Real.pi :=
    harg.2.2.trans (Complex.abs_arg_le_pi c)
  have hrv := hrot (logFlatSaddleRoot β k tStar c h).im (right_mem_uIcc)
  refine ⟨integrable_logFlatContourFunction_horizontal hβ ht.le hhpos hv
    (hc.le.trans hrv) k, ?_⟩
  have h1 := norm_integral_logFlatContourFunction_connector_le hβ ht hhpos hv hc hrot k y₂
  have h2 := norm_integral_logFlatContourFunction_left_le hβ ht hhpos hv hc hrv k y₂
  nlinarith

end InfiniteZero
