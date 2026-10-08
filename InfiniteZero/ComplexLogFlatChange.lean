import InfiniteZero.ComplexLogFlatPhase
import InfiniteZero.LogFlatIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The exact logarithmic substitution for the complex normal integral

The decreasing chart `t = tStar * exp (-y)` maps the half-line
`y > log (tStar / t₂)` onto `(0,t₂)`. The one-dimensional Lebesgue
change-of-variables theorem supplies its absolute Jacobian, including the
extra linear term in the complex log-flat phase.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

def complexLogFlatIntegrand (β tStar h : ℝ) (c : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ m * Complex.exp (-(β : ℂ) * (Real.log (tStar / t) : ℂ) ^ 2 -
    c * (t : ℂ) / (h : ℂ))

private theorem hasDerivAt_logarithmic_chart (tStar y : ℝ) :
    HasDerivAt (fun y : ℝ => tStar * Real.exp (-y)) (-tStar * Real.exp (-y)) y := by
  convert ((hasDerivAt_id y).neg.exp).const_mul tStar using 1
  simp

theorem logarithmic_chart_image {tStar t₂ : ℝ} (hStar : 0 < tStar) (ht₂ : 0 < t₂) :
    (fun y : ℝ => tStar * Real.exp (-y)) '' Ioi (Real.log (tStar / t₂)) = Ioo 0 t₂ := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    have ht : 0 < tStar * Real.exp (-y) := mul_pos hStar (Real.exp_pos _)
    refine ⟨ht, (Real.log_lt_log_iff ht ht₂).mp ?_⟩
    rw [Real.log_mul hStar.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [mem_Ioi, Real.log_div hStar.ne' ht₂.ne'] at hy
    linarith
  · intro ht
    refine ⟨Real.log (tStar / t), ?_, ?_⟩
    · rw [mem_Ioi, Real.log_div hStar.ne' ht.1.ne', Real.log_div hStar.ne' ht₂.ne']
      linarith [Real.log_lt_log ht.1 ht.2]
    · dsimp only
      rw [Real.exp_neg, Real.exp_log (div_pos hStar ht.1)]
      field_simp

private theorem logarithmic_chart_injective {tStar : ℝ} (hStar : 0 < tStar) :
    Function.Injective (fun y : ℝ => tStar * Real.exp (-y)) := by
  intro x y hxy
  exact neg_injective (Real.exp_injective (mul_left_cancel₀ hStar.ne' hxy))

/-- Lebesgue substitution, valid for any complex integrand. -/
theorem integral_logarithmic_substitution {tStar t₂ : ℝ}
    (hStar : 0 < tStar) (ht₂ : 0 < t₂) (f : ℝ → ℂ) :
    (∫ t in Ioo 0 t₂, f t) =
      ∫ y in Ioi (Real.log (tStar / t₂)),
        (tStar * Real.exp (-y)) • f (tStar * Real.exp (-y)) := by
  rw [← logarithmic_chart_image hStar ht₂]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun y _ => (hasDerivAt_logarithmic_chart tStar y).hasDerivWithinAt)
    (logarithmic_chart_injective hStar).injOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp only
  rw [abs_mul, abs_neg, abs_of_pos hStar, abs_of_pos (Real.exp_pos _)]

/-- The substitution also preserves absolute integrability with its Jacobian. -/
theorem integrableOn_logarithmic_substitution_iff {tStar t₂ : ℝ}
    (hStar : 0 < tStar) (ht₂ : 0 < t₂) (f : ℝ → ℂ) :
    IntegrableOn f (Ioo 0 t₂) ↔
      IntegrableOn (fun y : ℝ => (tStar * Real.exp (-y)) •
        f (tStar * Real.exp (-y))) (Ioi (Real.log (tStar / t₂))) := by
  rw [← logarithmic_chart_image hStar ht₂]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun y _ => (hasDerivAt_logarithmic_chart tStar y).hasDerivWithinAt)
    (logarithmic_chart_injective hStar).injOn]
  simp only [abs_mul, abs_neg, abs_of_pos hStar, abs_of_pos (Real.exp_pos _)]

theorem norm_complexLogFlatIntegrand (β tStar h : ℝ) (c : ℂ) (m : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖complexLogFlatIntegrand β tStar h c m t‖ =
      t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - c.re * t / h) := by
  simp [complexLogFlatIntegrand, norm_pow, Complex.norm_real, ← Complex.ofReal_pow,
    Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_exp, Complex.mul_re, Complex.div_ofReal_re]

/-- Absolute integrability at zero follows from the proved log-flat extension. -/
theorem integrableOn_complexLogFlatIntegrand {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (t₂ h : ℝ) (c : ℂ) (m : ℕ) :
    IntegrableOn (complexLogFlatIntegrand β tStar h c m) (Ioo 0 t₂) := by
  apply (integrableOn_logFlat_laplace hβ hStar t₂ c.re h m).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold complexLogFlatIntegrand
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (norm_complexLogFlatIntegrand β tStar h c m ht.1.le).le

/-- Pointwise identity including the Jacobian. The linear phase coefficient
is `m + 1`, rather than `m`. -/
theorem complexLogFlatIntegrand_logarithmic_chart {tStar : ℝ}
    (hStar : 0 < tStar) (β h : ℝ) (c : ℂ) (m : ℕ) (y : ℝ) :
    (tStar * Real.exp (-y)) •
        complexLogFlatIntegrand β tStar h c m (tStar * Real.exp (-y)) =
      (tStar : ℂ) ^ (m + 1) * Complex.exp
        (-logFlatComplexPhase β (m : ℝ) (c * (tStar : ℂ) / (h : ℂ)) (y : ℂ)) := by
  have hlog : Real.log (tStar / (tStar * Real.exp (-y))) = y := by
    rw [Real.log_div hStar.ne' (mul_pos hStar (Real.exp_pos _)).ne',
      Real.log_mul hStar.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hpow : ((tStar * Real.exp (-y) : ℝ) : ℂ) ^ (m + 1) =
      (tStar : ℂ) ^ (m + 1) *
        Complex.exp (-(((m : ℝ) + 1 : ℝ) : ℂ) * (y : ℂ)) := by
    push_cast
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  change ((tStar * Real.exp (-y) : ℝ) : ℂ) *
    complexLogFlatIntegrand β tStar h c m (tStar * Real.exp (-y)) = _
  unfold complexLogFlatIntegrand
  rw [hlog]
  calc
    _ = ((tStar * Real.exp (-y) : ℝ) : ℂ) ^ (m + 1) *
        Complex.exp (-(β : ℂ) * (y : ℂ) ^ 2 -
          c * ((tStar * Real.exp (-y) : ℝ) : ℂ) / (h : ℂ)) := by
      rw [pow_succ]
      ring
    _ = (tStar : ℂ) ^ (m + 1) * (Complex.exp
        (-(((m : ℝ) + 1 : ℝ) : ℂ) * (y : ℂ)) *
        Complex.exp (-(β : ℂ) * (y : ℂ) ^ 2 -
          c * ((tStar * Real.exp (-y) : ℝ) : ℂ) / (h : ℂ))) := by rw [hpow, mul_assoc]
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      unfold logFlatComplexPhase
      push_cast
      ring

/-- Exact logarithmic form of the physical normal integral. -/
theorem integral_complexLogFlat_logarithmic_change {tStar t₂ : ℝ}
    (hStar : 0 < tStar) (ht₂ : 0 < t₂) (β h : ℝ) (c : ℂ) (m : ℕ) :
    (∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t) =
      (tStar : ℂ) ^ (m + 1) *
        ∫ y in Ioi (Real.log (tStar / t₂)), Complex.exp
          (-logFlatComplexPhase β (m : ℝ) (c * (tStar : ℂ) / (h : ℂ)) (y : ℂ)) := by
  rw [integral_logarithmic_substitution hStar ht₂, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun y _ =>
    complexLogFlatIntegrand_logarithmic_chart hStar β h c m y

/-- Integrability of the logarithmic half-line integral is proved, not assumed. -/
theorem integrableOn_logFlatComplexPhase_halfline {β tStar t₂ : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₂ : 0 < t₂)
    (h : ℝ) (c : ℂ) (m : ℕ) :
    IntegrableOn (fun y : ℝ => Complex.exp
      (-logFlatComplexPhase β (m : ℝ) (c * (tStar : ℂ) / (h : ℂ)) (y : ℂ)))
      (Ioi (Real.log (tStar / t₂))) := by
  have hi := (integrableOn_logarithmic_substitution_iff hStar ht₂
    (complexLogFlatIntegrand β tStar h c m)).mp
      (integrableOn_complexLogFlatIntegrand hβ hStar t₂ h c m)
  have he : (fun y : ℝ => (tStar * Real.exp (-y)) •
      complexLogFlatIntegrand β tStar h c m (tStar * Real.exp (-y))) =
      (fun y : ℝ => (tStar : ℂ) ^ (m + 1) * Complex.exp
        (-logFlatComplexPhase β (m : ℝ) (c * (tStar : ℂ) / (h : ℂ)) (y : ℂ))) := by
    funext y
    exact complexLogFlatIntegrand_logarithmic_chart hStar β h c m y
  rw [he] at hi
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero (m + 1)
    (Complex.ofReal_ne_zero.mpr hStar.ne'))) _).mp hi

end InfiniteZero
