import InfiniteZero.ComplexLogFlatContour

/-!
# Log-flat contour displacement with a locally holomorphic multiplier

The multiplier is differentiable only on the closed half-strip used by the
contour. A bound on that same half-strip preserves the Gaussian majorant,
so the right connector disappears and both horizontal rays are integrable.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace InfiniteZero

/-- The closed half-strip swept out by a horizontal ray shifted by `v * I`.
The vertical interval is unoriented, allowing either sign of `v`. -/
def logFlatContourHalfStrip (a v : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.im ∈ uIcc 0 v}

theorem mem_logFlatContourHalfStrip {a v x η : ℝ}
    (hx : a ≤ x) (hη : η ∈ uIcc 0 v) :
    (x : ℂ) + (η : ℂ) * Complex.I ∈ logFlatContourHalfStrip a v := by
  simpa [logFlatContourHalfStrip] using And.intro hx hη

def logFlatComplexMultiplierIntegrand (β k : ℝ) (C : ℂ) (B : ℂ → ℂ) (z : ℂ) : ℂ :=
  logFlatComplexIntegrand β k C z * B z

theorem differentiableOn_logFlatComplexMultiplierIntegrand
    (β k : ℝ) (C : ℂ) {B : ℂ → ℂ} {a v : ℝ}
    (hB : DifferentiableOn ℂ B (logFlatContourHalfStrip a v)) :
    DifferentiableOn ℂ (logFlatComplexMultiplierIntegrand β k C B)
      (logFlatContourHalfStrip a v) :=
  (differentiable_logFlatComplexIntegrand β k C).differentiableOn.mul hB

/-- The finite contour lies entirely in the domain of the multiplier. -/
theorem logFlatComplex_multiplier_rectangle (β k : ℝ) (C : ℂ)
    {B : ℂ → ℂ} {a b v : ℝ} (hab : a ≤ b)
    (hB : DifferentiableOn ℂ B (logFlatContourHalfStrip a v)) :
    (∫ x in a..b, logFlatComplexMultiplierIntegrand β k C B (x : ℂ)) =
      Complex.I * (∫ η in 0..v,
        logFlatComplexMultiplierIntegrand β k C B ((a : ℂ) + (η : ℂ) * Complex.I)) +
      (∫ x in a..b,
        logFlatComplexMultiplierIntegrand β k C B ((x : ℂ) + (v : ℂ) * Complex.I)) -
      Complex.I * (∫ η in 0..v,
        logFlatComplexMultiplierIntegrand β k C B ((b : ℂ) + (η : ℂ) * Complex.I)) := by
  have hd : DifferentiableOn ℂ (logFlatComplexMultiplierIntegrand β k C B)
      (uIcc a b ×ℂ uIcc 0 v) := by
    apply (differentiableOn_logFlatComplexMultiplierIntegrand β k C hB).mono
    intro z hz
    change z.re ∈ uIcc a b ∧ z.im ∈ uIcc 0 v at hz
    exact ⟨(show z.re ∈ Icc a b by simpa only [uIcc_of_le hab] using hz.1).1, hz.2⟩
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (logFlatComplexMultiplierIntegrand β k C B) (a : ℂ) ((b : ℂ) + (v : ℂ) * Complex.I)
    (by simpa using hd)
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_add, mul_one, Complex.ofReal_zero, smul_eq_mul] at h
  linear_combination h

private theorem abs_le_abs_of_mem_zero_uIcc {η v : ℝ} (hη : η ∈ uIcc 0 v) :
    |η| ≤ |v| := by
  rcases le_total 0 v with hv | hv
  · rw [uIcc_of_le hv] at hη
    rw [abs_of_nonneg hη.1, abs_of_nonneg hv]
    exact hη.2
  · rw [uIcc_of_ge hv] at hη
    rw [abs_of_nonpos hη.2, abs_of_nonpos hv]
    exact neg_le_neg hη.1

/-- Multiplication costs only the uniform bound `K` in the Gaussian estimate. -/
theorem norm_logFlatComplexMultiplierIntegrand_le {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) {B : ℂ → ℂ} {a v K x η : ℝ}
    (hbound : ∀ z ∈ logFlatContourHalfStrip a v, ‖B z‖ ≤ K)
    (hx : a ≤ x) (hη : η ∈ uIcc 0 v) :
    ‖logFlatComplexMultiplierIntegrand β k C B ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      K * logFlatContourMajorant β k C a v * Real.exp (-(β / 2) * x ^ 2) := by
  rw [logFlatComplexMultiplierIntegrand, norm_mul]
  calc
    _ ≤ (logFlatContourMajorant β k C a v * Real.exp (-(β / 2) * x ^ 2)) * K :=
      mul_le_mul (norm_logFlatComplexIntegrand_le hβ k C hx
        (abs_le_abs_of_mem_zero_uIcc hη))
        (hbound _ (mem_logFlatContourHalfStrip hx hη)) (norm_nonneg _)
        (by unfold logFlatContourMajorant; positivity)
    _ = _ := by ring

/-- Every horizontal ray inside the closed half-strip is absolutely integrable. -/
theorem integrableOn_logFlatComplexMultiplierIntegrand_ray {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) {B : ℂ → ℂ} {a v K η : ℝ}
    (hB : DifferentiableOn ℂ B (logFlatContourHalfStrip a v))
    (hbound : ∀ z ∈ logFlatContourHalfStrip a v, ‖B z‖ ≤ K)
    (hη : η ∈ uIcc 0 v) :
    IntegrableOn
      (fun x : ℝ => logFlatComplexMultiplierIntegrand β k C B
        ((x : ℂ) + (η : ℂ) * Complex.I)) (Ioi a) := by
  have hc : ContinuousOn
      (fun x : ℝ => logFlatComplexMultiplierIntegrand β k C B
        ((x : ℂ) + (η : ℂ) * Complex.I)) (Ioi a) :=
    (differentiableOn_logFlatComplexMultiplierIntegrand β k C hB).continuousOn.comp
      (show Continuous (fun x : ℝ => (x : ℂ) + (η : ℂ) * Complex.I) by fun_prop).continuousOn
      (fun x hx => mem_logFlatContourHalfStrip (le_of_lt hx) hη)
  apply ((integrable_exp_neg_mul_sq (half_pos hβ)).const_mul
    (K * logFlatContourMajorant β k C a v)).integrableOn.mono'
      (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_logFlatComplexMultiplierIntegrand_le hβ k C hbound (le_of_lt hx) hη

/-- Finite vertical connectors are genuine integrals, using only the same
local differentiability assumption. -/
theorem intervalIntegrable_logFlatComplexMultiplierIntegrand_vertical
    (β k : ℝ) (C : ℂ) {B : ℂ → ℂ} {a b v : ℝ}
    (hB : DifferentiableOn ℂ B (logFlatContourHalfStrip a v)) (hab : a ≤ b) :
    IntervalIntegrable
      (fun η : ℝ => logFlatComplexMultiplierIntegrand β k C B
        ((b : ℂ) + (η : ℂ) * Complex.I)) volume 0 v := by
  apply ContinuousOn.intervalIntegrable
  exact (differentiableOn_logFlatComplexMultiplierIntegrand β k C hB).continuousOn.comp
    (show Continuous (fun η : ℝ => (b : ℂ) + (η : ℂ) * Complex.I) by fun_prop).continuousOn
    (fun η hη => mem_logFlatContourHalfStrip hab hη)

/-- Gaussian decay of the whole right connector, uniform in its height. -/
theorem norm_logFlatComplexMultiplier_verticalIntegral_le {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) {B : ℂ → ℂ} {a b v K : ℝ} (hab : a ≤ b)
    (hbound : ∀ z ∈ logFlatContourHalfStrip a v, ‖B z‖ ≤ K) :
    ‖∫ η in 0..v,
      logFlatComplexMultiplierIntegrand β k C B ((b : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      K * logFlatContourMajorant β k C a v * Real.exp (-(β / 2) * b ^ 2) * |v| := by
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun η hη => norm_logFlatComplexMultiplierIntegrand_le hβ k C hbound hab
      (uIoc_subset_uIcc hη))

/-- Boundedness on the half-strip suffices to remove the right connector. -/
theorem tendsto_logFlatComplexMultiplier_verticalIntegral {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) {B : ℂ → ℂ} {a v K : ℝ}
    (hbound : ∀ z ∈ logFlatContourHalfStrip a v, ‖B z‖ ≤ K) :
    Tendsto (fun b : ℝ => ∫ η in 0..v,
      logFlatComplexMultiplierIntegrand β k C B ((b : ℂ) + (η : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  have hgauss : Tendsto (fun b : ℝ => Real.exp (-(β / 2) * b ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
        (neg_neg_of_pos (half_pos hβ)))
  have hmajor : Tendsto (fun b : ℝ =>
      K * logFlatContourMajorant β k C a v * Real.exp (-(β / 2) * b ^ 2) * |v|)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hgauss.const_mul (K * logFlatContourMajorant β k C a v)).mul_const |v|
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_ge_atTop a] with b hb
  exact norm_logFlatComplexMultiplier_verticalIntegral_le hβ k C hb hbound

/-- Exact half-ray shift with a multiplier holomorphic only on the swept
half-strip. No global holomorphy or sign restriction on `C` is used. -/
theorem logFlatComplex_multiplier_ray_shift {β : ℝ} (hβ : 0 < β)
    (k : ℝ) (C : ℂ) (a v : ℝ) {B : ℂ → ℂ} {K : ℝ}
    (hB : DifferentiableOn ℂ B (logFlatContourHalfStrip a v)) (_hK : 0 ≤ K)
    (hbound : ∀ z ∈ logFlatContourHalfStrip a v, ‖B z‖ ≤ K) :
    (∫ x in Ioi a, logFlatComplexMultiplierIntegrand β k C B (x : ℂ)) =
      Complex.I * (∫ η in 0..v,
        logFlatComplexMultiplierIntegrand β k C B ((a : ℂ) + (η : ℂ) * Complex.I)) +
      (∫ x in Ioi a,
        logFlatComplexMultiplierIntegrand β k C B ((x : ℂ) + (v : ℂ) * Complex.I)) := by
  have hbot : IntegrableOn
      (fun x : ℝ => logFlatComplexMultiplierIntegrand β k C B (x : ℂ)) (Ioi a) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      integrableOn_logFlatComplexMultiplierIntegrand_ray hβ k C hB hbound
        (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 v)
  have htbot := intervalIntegral_tendsto_integral_Ioi a hbot tendsto_id
  have httop := intervalIntegral_tendsto_integral_Ioi a
    (integrableOn_logFlatComplexMultiplierIntegrand_ray hβ k C hB hbound right_mem_uIcc) tendsto_id
  have htright := tendsto_logFlatComplexMultiplier_verticalIntegral hβ k C hbound
  have ht := (httop.const_add (Complex.I * (∫ η in 0..v,
      logFlatComplexMultiplierIntegrand β k C B ((a : ℂ) + (η : ℂ) * Complex.I)))).sub
    (htright.const_mul Complex.I)
  simp only [mul_zero, sub_zero] at ht
  have htexact := ht.congr' (by
    filter_upwards [eventually_ge_atTop a] with b hb
    exact (logFlatComplex_multiplier_rectangle β k C hb hB).symm)
  exact tendsto_nhds_unique htbot htexact

end InfiniteZero
