import InfiniteZero.ComplexLambertRoot
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exact complex log-flat critical-point identities

The coefficient C is c*tStar/h in logarithmic coordinates. The linear term
is k+1, including the Jacobian. The critical point is supplied by the proved
Lambert construction, not by an asymptotic saddle hypothesis.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

def logFlatComplexPhase (β k : ℝ) (C y : ℂ) : ℂ :=
  (β : ℂ) * y ^ 2 + C * Complex.exp (-y) + ((k + 1 : ℝ) : ℂ) * y

def logFlatComplexCritical (β k : ℝ) (w : ℂ) : ℂ :=
  w - (((k + 1) / (2 * β) : ℝ) : ℂ)

theorem hasDerivAt_logFlatComplexPhase (β k : ℝ) (C y : ℂ) :
    HasDerivAt (logFlatComplexPhase β k C)
      (2 * (β : ℂ) * y - C * Complex.exp (-y) + ((k + 1 : ℝ) : ℂ)) y := by
  convert (((hasDerivAt_id y).pow 2).const_mul (β : ℂ) |>.add
    (((hasDerivAt_id y).neg.cexp).const_mul C)).add
    ((hasDerivAt_id y).const_mul ((k + 1 : ℝ) : ℂ)) using 1
  simp
  ring

theorem deriv_logFlatComplexPhase (β k : ℝ) (C y : ℂ) :
    deriv (logFlatComplexPhase β k C) y =
      2 * (β : ℂ) * y - C * Complex.exp (-y) + ((k + 1 : ℝ) : ℂ) :=
  (hasDerivAt_logFlatComplexPhase β k C y).deriv

theorem deriv2_logFlatComplexPhase (β k : ℝ) (C y : ℂ) :
    deriv (deriv (logFlatComplexPhase β k C)) y =
      2 * (β : ℂ) + C * Complex.exp (-y) := by
  have he : deriv (logFlatComplexPhase β k C) = fun z =>
      2 * (β : ℂ) * z - C * Complex.exp (-z) + ((k + 1 : ℝ) : ℂ) := by
    funext z
    exact deriv_logFlatComplexPhase β k C z
  rw [he]
  convert ((((hasDerivAt_id y).const_mul (2 * (β : ℂ))).sub
    (((hasDerivAt_id y).neg.cexp).const_mul C)).add_const ((k + 1 : ℝ) : ℂ)).deriv using 1
  simp

theorem logFlat_critical_exponential {β k : ℝ} (hβ : β ≠ 0) {C w : ℂ}
    (hw : w * Complex.exp w = C * Complex.exp (((k + 1) / (2 * β) : ℝ) : ℂ) /
      (2 * (β : ℂ))) :
    C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w := by
  have hb : (2 : ℂ) * (β : ℂ) ≠ 0 := by exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hβ)
  have he : -logFlatComplexCritical β k w =
      (((k + 1) / (2 * β) : ℝ) : ℂ) - w := by simp [logFlatComplexCritical]
  rw [he, Complex.exp_sub]
  rw [← mul_div_assoc]
  apply (div_eq_iff (Complex.exp_ne_zero w)).mpr
  have h := (eq_div_iff hb).mp hw
  linear_combination -h

theorem logFlatComplexCritical_deriv_eq_zero {β k : ℝ} (hβ : β ≠ 0) {C w : ℂ}
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w) :
    deriv (logFlatComplexPhase β k C) (logFlatComplexCritical β k w) = 0 := by
  rw [deriv_logFlatComplexPhase, hc]
  unfold logFlatComplexCritical
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hβ]
  ring

theorem logFlatComplexCritical_value {β k : ℝ} (hβ : β ≠ 0) {C w : ℂ}
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w) :
    logFlatComplexPhase β k C (logFlatComplexCritical β k w) =
      (β : ℂ) * (w ^ 2 + 2 * w) - (((k + 1) ^ 2 / (4 * β) : ℝ) : ℂ) := by
  unfold logFlatComplexPhase
  rw [hc]
  unfold logFlatComplexCritical
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hβ]
  ring

theorem logFlatComplexCritical_hessian (β k : ℝ) {C w : ℂ}
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w) :
    deriv (deriv (logFlatComplexPhase β k C)) (logFlatComplexCritical β k w) =
      2 * (β : ℂ) * (1 + w) := by
  rw [deriv2_logFlatComplexPhase, hc]
  ring

theorem logFlatComplexPhase_difference {β k : ℝ} (hβ : β ≠ 0) {C w : ℂ}
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w)
    (q : ℂ) :
    logFlatComplexPhase β k C (logFlatComplexCritical β k w + q) -
      logFlatComplexPhase β k C (logFlatComplexCritical β k w) =
        (β : ℂ) * q ^ 2 + 2 * (β : ℂ) * w * (Complex.exp (-q) - 1 + q) := by
  have he : Complex.exp (-(logFlatComplexCritical β k w + q)) =
      Complex.exp (-logFlatComplexCritical β k w) * Complex.exp (-q) := by
    rw [neg_add, Complex.exp_add]
  unfold logFlatComplexPhase
  rw [he, ← mul_assoc C, hc]
  unfold logFlatComplexCritical
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hβ]
  ring

def exponentialRemainder (q : ℝ) : ℝ := Real.exp (-q) - 1 + q

theorem exponentialRemainder_nonneg (q : ℝ) : 0 ≤ exponentialRemainder q := by
  have := Real.add_one_le_exp (-q)
  dsimp [exponentialRemainder]
  linarith

def horizontalSaddlePhase (β : ℝ) (w : ℂ) (q : ℝ) : ℂ :=
  (β : ℂ) * (q : ℂ) ^ 2 + 2 * (β : ℂ) * w * (exponentialRemainder q : ℂ)

theorem horizontalSaddlePhase_re (β : ℝ) (w : ℂ) (q : ℝ) :
    (horizontalSaddlePhase β w q).re = β * q ^ 2 + 2 * β * w.re * exponentialRemainder q := by
  simp [horizontalSaddlePhase, ← Complex.ofReal_pow, Complex.mul_re]

theorem norm_exp_neg_horizontalSaddlePhase_le {β : ℝ} (hβ : 0 ≤ β) {w : ℂ}
    (hw : 0 ≤ w.re) (q : ℝ) :
    ‖Complex.exp (-horizontalSaddlePhase β w q)‖ ≤ Real.exp (-β * q ^ 2) := by
  rw [Complex.norm_exp, Complex.neg_re, horizontalSaddlePhase_re]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hβ) hw)
    (exponentialRemainder_nonneg q)]

theorem integrable_exp_neg_horizontalSaddlePhase {β : ℝ} (hβ : 0 < β) {w : ℂ}
    (hw : 0 ≤ w.re) : Integrable (fun q : ℝ => Complex.exp (-horizontalSaddlePhase β w q)) := by
  apply (integrable_exp_neg_mul_sq hβ).mono' (Continuous.aestronglyMeasurable ?_) ?_
  · unfold horizontalSaddlePhase exponentialRemainder
    fun_prop
  · exact Filter.Eventually.of_forall (norm_exp_neg_horizontalSaddlePhase_le hβ.le hw)

end InfiniteZero
