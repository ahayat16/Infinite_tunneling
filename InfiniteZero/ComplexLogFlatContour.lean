import InfiniteZero.ComplexLogFlatPhase
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Exact displacement of a log-flat integration ray

Cauchy's theorem on rectangles and Gaussian decay on a fixed horizontal
strip give the contour identity. The coefficient `C` is arbitrary: this
step uses no sign or saddle-point assumption on it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace InfiniteZero

def logFlatComplexIntegrand (β k : ℝ) (C z : ℂ) : ℂ :=
  Complex.exp (-logFlatComplexPhase β k C z)

theorem differentiable_logFlatComplexIntegrand (β k : ℝ) (C : ℂ) :
    Differentiable ℂ (logFlatComplexIntegrand β k C) := by
  intro z
  exact ((hasDerivAt_logFlatComplexPhase β k C z).neg.cexp).differentiableAt

theorem continuous_logFlatComplexIntegrand (β k : ℝ) (C : ℂ) :
    Continuous (logFlatComplexIntegrand β k C) :=
  (differentiable_logFlatComplexIntegrand β k C).continuous

/-- The finite-rectangle identity is valid for either sign of the vertical displacement. -/
theorem logFlatComplex_rectangle (β k : ℝ) (C : ℂ) (a b v : ℝ) :
    (∫ x in a..b, logFlatComplexIntegrand β k C (x : ℂ)) =
      Complex.I * (∫ η in 0..v,
        logFlatComplexIntegrand β k C ((a : ℂ) + (η : ℂ) * Complex.I)) +
      (∫ x in a..b,
        logFlatComplexIntegrand β k C ((x : ℂ) + (v : ℂ) * Complex.I)) -
      Complex.I * (∫ η in 0..v,
        logFlatComplexIntegrand β k C ((b : ℂ) + (η : ℂ) * Complex.I)) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (logFlatComplexIntegrand β k C) (a : ℂ) ((b : ℂ) + (v : ℂ) * Complex.I)
    (differentiable_logFlatComplexIntegrand β k C).differentiableOn
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_add, mul_one, Complex.ofReal_zero, smul_eq_mul] at h
  linear_combination h

/-- Real part of the phase along a horizontal strip. -/
theorem logFlatComplexPhase_re (β k x η : ℝ) (C : ℂ) :
    (logFlatComplexPhase β k C ((x : ℂ) + (η : ℂ) * Complex.I)).re =
      β * (x ^ 2 - η ^ 2) +
        (C * Complex.exp (-((x : ℂ) + (η : ℂ) * Complex.I))).re + (k + 1) * x := by
  simp [logFlatComplexPhase, Complex.mul_re, Complex.mul_im, pow_two]

def logFlatContourMajorant (β k : ℝ) (C : ℂ) (a v : ℝ) : ℝ :=
  Real.exp (β * v ^ 2 + (k + 1) ^ 2 / (2 * β) + ‖C‖ * Real.exp (-a))

/-- A Gaussian bound uniform on the part of a fixed strip to the right of `a`. -/
theorem norm_logFlatComplexIntegrand_le {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) {a v x η : ℝ} (hx : a ≤ x) (hη : |η| ≤ |v|) :
    ‖logFlatComplexIntegrand β k C ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      logFlatContourMajorant β k C a v * Real.exp (-(β / 2) * x ^ 2) := by
  have hterm : -(C * Complex.exp (-((x : ℂ) + (η : ℂ) * Complex.I))).re ≤
      ‖C‖ * Real.exp (-a) := by
    apply ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    gcongr
  have hsq : η ^ 2 ≤ v ^ 2 := sq_le_sq.mpr hη
  have hlinear : -(k + 1) * x ≤ β / 2 * x ^ 2 + (k + 1) ^ 2 / (2 * β) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * β by positivity)).mp
    have hs := sq_nonneg (β * x + (k + 1))
    have he : (2 * β) * (β / 2 * x ^ 2 + (k + 1) ^ 2 / (2 * β)) =
        β ^ 2 * x ^ 2 + (k + 1) ^ 2 := by field_simp
    nlinarith [he]
  rw [logFlatComplexIntegrand, Complex.norm_exp, Complex.neg_re,
    logFlatComplexPhase_re, logFlatContourMajorant, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hβ.le]

/-- Every fixed horizontal ray is absolutely integrable. -/
theorem integrableOn_logFlatComplexIntegrand_ray {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) (a v : ℝ) :
    IntegrableOn
      (fun x : ℝ => logFlatComplexIntegrand β k C ((x : ℂ) + (v : ℂ) * Complex.I))
      (Ioi a) := by
  have hc : Continuous
      (fun x : ℝ => logFlatComplexIntegrand β k C ((x : ℂ) + (v : ℂ) * Complex.I)) :=
    (continuous_logFlatComplexIntegrand β k C).comp (by fun_prop)
  apply ((integrable_exp_neg_mul_sq (half_pos hβ)).const_mul
    (logFlatContourMajorant β k C a v)).integrableOn.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_logFlatComplexIntegrand_le hβ k C (show a < x from hx).le le_rfl

private theorem abs_le_abs_of_mem_zero_uIoc {η v : ℝ} (hη : η ∈ Ι 0 v) : |η| ≤ |v| := by
  rcases mem_uIoc.mp hη with hη | hη
  · rw [abs_of_pos hη.1]
    exact hη.2.trans (le_abs_self v)
  · rw [abs_of_nonpos hη.2]
    exact (neg_le_neg hη.1.le).trans (neg_le_abs v)

/-- The entire right connector has a Gaussian bound in its real coordinate. -/
theorem norm_logFlatComplex_verticalIntegral_le {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) {a b : ℝ} (hab : a ≤ b) (v : ℝ) :
    ‖∫ η in 0..v, logFlatComplexIntegrand β k C ((b : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      logFlatContourMajorant β k C a v * Real.exp (-(β / 2) * b ^ 2) * |v| := by
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun η hη => norm_logFlatComplexIntegrand_le hβ k C hab (abs_le_abs_of_mem_zero_uIoc hη))

/-- The right connector disappears as the rectangle extends to infinity. -/
theorem tendsto_logFlatComplex_verticalIntegral {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) (v : ℝ) :
    Tendsto (fun b : ℝ => ∫ η in 0..v,
      logFlatComplexIntegrand β k C ((b : ℂ) + (η : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hgauss : Tendsto (fun b : ℝ => Real.exp (-(β / 2) * b ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
        (neg_neg_of_pos (half_pos hβ)))
  have hbound : Tendsto (fun b : ℝ =>
      logFlatContourMajorant β k C 0 v * Real.exp (-(β / 2) * b ^ 2) * |v|)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hgauss.const_mul (logFlatContourMajorant β k C 0 v)).mul_const |v|
  apply squeeze_zero_norm' _ hbound
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  exact norm_logFlatComplex_verticalIntegral_le hβ k C hb v

/-- Exact displacement of the integration ray, including the left connector. -/
theorem logFlatComplex_ray_shift {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) (a v : ℝ) :
    (∫ x in Ioi a, logFlatComplexIntegrand β k C (x : ℂ)) =
      Complex.I * (∫ η in 0..v,
        logFlatComplexIntegrand β k C ((a : ℂ) + (η : ℂ) * Complex.I)) +
      (∫ x in Ioi a,
        logFlatComplexIntegrand β k C ((x : ℂ) + (v : ℂ) * Complex.I)) := by
  have hbot : IntegrableOn (fun x : ℝ => logFlatComplexIntegrand β k C (x : ℂ)) (Ioi a) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      integrableOn_logFlatComplexIntegrand_ray hβ k C a 0
  have htbot := intervalIntegral_tendsto_integral_Ioi a hbot tendsto_id
  have httop := intervalIntegral_tendsto_integral_Ioi a
    (integrableOn_logFlatComplexIntegrand_ray hβ k C a v) tendsto_id
  have htright := tendsto_logFlatComplex_verticalIntegral hβ k C v
  have ht := (httop.const_add (Complex.I * (∫ η in 0..v,
      logFlatComplexIntegrand β k C ((a : ℂ) + (η : ℂ) * Complex.I)))).sub
    (htright.const_mul Complex.I)
  simp only [mul_zero, sub_zero] at ht
  have htexact := ht.congr (fun b => (logFlatComplex_rectangle β k C a b v).symm)
  exact tendsto_nhds_unique htbot htexact

end InfiniteZero
