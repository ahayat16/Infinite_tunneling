import InfiniteZero.ExponentialRemainderBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Leading asymptotic of the horizontal complex saddle integral

This module concerns the horizontal integral through a critical point.
It does not identify it with an undeformed original contour integral.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def horizontalSaddleIntegral (β : ℝ) (w : ℂ) : ℂ :=
  ∫ q : ℝ, Complex.exp (-horizontalSaddlePhase β w q)

def scaledHorizontalSaddle (β A v x : ℝ) : ℂ :=
  Complex.exp (-horizontalSaddlePhase β ((A : ℂ) + (v : ℂ) * Complex.I)
    (x / Real.sqrt A))

theorem horizontalSaddlePhase_real_im (β A v q : ℝ) :
    horizontalSaddlePhase β ((A : ℂ) + (v : ℂ) * Complex.I) q =
      ((β * q ^ 2 + 2 * β * (A * exponentialRemainder q) : ℝ) : ℂ) +
        ((2 * β * (v * exponentialRemainder q) : ℝ) : ℂ) * Complex.I := by
  unfold horizontalSaddlePhase
  push_cast
  ring

theorem continuous_scaledHorizontalSaddle (β A v : ℝ) :
    Continuous (scaledHorizontalSaddle β A v) := by
  unfold scaledHorizontalSaddle horizontalSaddlePhase exponentialRemainder
  fun_prop

theorem norm_scaledHorizontalSaddle (β A v x : ℝ) :
    ‖scaledHorizontalSaddle β A v x‖ =
      Real.exp (-β * (x / Real.sqrt A) ^ 2 -
        2 * β * (A * exponentialRemainder (x / Real.sqrt A))) := by
  rw [scaledHorizontalSaddle, Complex.norm_exp, Complex.neg_re,
    horizontalSaddlePhase_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  congr 1
  ring

private theorem tendsto_bounded_mul_exponentialRemainder
    {ι : Type*} {l : Filter ι} {q v : ι → ℝ} {M : ℝ}
    (hq : Tendsto q l (𝓝 0)) (hv : ∀ᶠ i in l, |v i| ≤ M) :
    Tendsto (fun i => v i * exponentialRemainder (q i)) l (𝓝 0) := by
  have hc : Continuous exponentialRemainder := by
    unfold exponentialRemainder
    fun_prop
  have hu : Tendsto (fun i => exponentialRemainder (q i)) l (𝓝 0) := by
    simpa [exponentialRemainder] using (hc.tendsto 0).comp hq
  have hbound : Tendsto (fun i => M * ‖exponentialRemainder (q i)‖) l (𝓝 0) := by
    simpa using hu.norm.const_mul M
  apply squeeze_zero_norm' _ hbound
  filter_upwards [hv] with i hi
  rw [norm_mul, Real.norm_eq_abs (v i)]
  exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)

/-- The imaginary part may vary arbitrarily, provided it stays bounded. -/
theorem tendsto_scaledHorizontalSaddle
    {ι : Type*} {l : Filter ι} {A v : ι → ℝ} {M : ℝ}
    (hA : Tendsto A l atTop) (hv : ∀ᶠ i in l, |v i| ≤ M) (β x : ℝ) :
    Tendsto (fun i => scaledHorizontalSaddle β (A i) (v i) x) l
      (𝓝 (Complex.exp ((-β * x ^ 2 : ℝ) : ℂ))) := by
  have hq : Tendsto (fun i => x / Real.sqrt (A i)) l (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp hA).const_div_atTop x
  have hu := (tendsto_scaled_exponentialRemainder x).comp hA
  have hvu := tendsto_bounded_mul_exponentialRemainder hq hv
  have hre : Tendsto
      (fun i => β * (x / Real.sqrt (A i)) ^ 2 +
        2 * β * (A i * exponentialRemainder (x / Real.sqrt (A i))))
      l (𝓝 (β * x ^ 2)) := by
    have he : β * (0 : ℝ) ^ 2 + 2 * β * (x ^ 2 / 2) = β * x ^ 2 := by ring
    simpa only [he] using ((hq.pow 2).const_mul β).add (hu.const_mul (2 * β))
  have him : Tendsto
      (fun i => 2 * β * (v i * exponentialRemainder (x / Real.sqrt (A i))))
      l (𝓝 0) := by simpa using hvu.const_mul (2 * β)
  have hp : Tendsto
      (fun i => horizontalSaddlePhase β ((A i : ℂ) + (v i : ℂ) * Complex.I)
        (x / Real.sqrt (A i))) l (𝓝 ((β * x ^ 2 : ℝ) : ℂ)) := by
    simpa only [horizontalSaddlePhase_real_im, Complex.ofReal_zero, zero_mul, add_zero]
      using hre.ofReal.add (him.ofReal.mul_const Complex.I)
  simpa only [scaledHorizontalSaddle, Complex.ofReal_neg, neg_mul] using hp.neg.cexp

/-- A single integrable bound works for all `A ≥ 1` and every imaginary part. -/
theorem norm_scaledHorizontalSaddle_le {β A : ℝ} (hβ : 0 ≤ β) (hA : 1 ≤ A)
    (v x : ℝ) :
    ‖scaledHorizontalSaddle β A v x‖ ≤
      Real.exp (-(β * Real.exp (-1)) * min (x ^ 2) |x|) := by
  rw [norm_scaledHorizontalSaddle]
  apply Real.exp_le_exp.mpr
  have hb := mul_le_mul_of_nonneg_left (exponentialRemainder_scaled_lower hA x)
    (show 0 ≤ 2 * β by positivity)
  have hsq := mul_nonneg hβ (sq_nonneg (x / Real.sqrt A))
  nlinarith

/-- The elementary exponential majorant is integrable on both half-lines. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  have hs : Iic (0 : ℝ) ∪ Ioi 0 = univ := Iic_union_Ioi
  rw [← integrableOn_univ, ← hs, integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic ha 0).congr_fun _ measurableSet_Iic
    intro x hx
    change x ≤ 0 at hx
    dsimp only
    rw [abs_of_nonpos hx]
    congr 1
    ring
  · apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    dsimp only
    rw [abs_of_pos hx]

/-- Quadratic near zero and linear at infinity is enough for domination. -/
theorem integrable_exp_neg_mul_min_sq_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * min (x ^ 2) |x|)) := by
  apply ((integrable_exp_neg_mul_sq ha).add (integrable_exp_neg_mul_abs ha)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total (x ^ 2) |x| with hx | hx
  · rw [min_eq_left hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [min_eq_right hx]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- The scaled integral is exactly the normalized horizontal integral. -/
theorem integral_scaledHorizontalSaddle_eq {β A v : ℝ} (hA : 0 < A) :
    (∫ x : ℝ, scaledHorizontalSaddle β A v x) =
      (Real.sqrt A : ℂ) * horizontalSaddleIntegral β ((A : ℂ) + (v : ℂ) * Complex.I) := by
  unfold scaledHorizontalSaddle horizontalSaddleIntegral
  simp only [div_eq_mul_inv]
  rw [Measure.integral_comp_mul_right
    (fun q : ℝ => Complex.exp (-horizontalSaddlePhase β ((A : ℂ) + (v : ℂ) * Complex.I) q))
    (Real.sqrt A)⁻¹]
  rw [inv_inv, abs_of_pos (Real.sqrt_pos.2 hA)]
  simp only [Complex.real_smul]

/-- Dominated convergence gives the genuine Gaussian leading coefficient. -/
theorem tendsto_integral_scaledHorizontalSaddle
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {β M : ℝ} {A v : ι → ℝ} (hβ : 0 < β)
    (hA : Tendsto A l atTop) (hv : ∀ᶠ i in l, |v i| ≤ M) :
    Tendsto (fun i => ∫ x : ℝ, scaledHorizontalSaddle β (A i) (v i) x) l
      (𝓝 ((Real.sqrt (Real.pi / β) : ℝ) : ℂ)) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume)
    (fun x : ℝ => Real.exp (-(β * Real.exp (-1)) * min (x ^ 2) |x|))
    (Eventually.of_forall fun i =>
      (continuous_scaledHorizontalSaddle β (A i) (v i)).aestronglyMeasurable)
    (show ∀ᶠ i in l, ∀ᵐ x : ℝ, ‖scaledHorizontalSaddle β (A i) (v i) x‖ ≤
        Real.exp (-(β * Real.exp (-1)) * min (x ^ 2) |x|) from by
      filter_upwards [hA.eventually (eventually_ge_atTop (1 : ℝ))] with i hi
      exact Eventually.of_forall (norm_scaledHorizontalSaddle_le hβ.le hi (v i)))
    (integrable_exp_neg_mul_min_sq_abs (mul_pos hβ (Real.exp_pos _)))
    (Eventually.of_forall (tendsto_scaledHorizontalSaddle hA hv β))
  have hgauss : (∫ x : ℝ, Complex.exp ((-β * x ^ 2 : ℝ) : ℂ)) =
      ((Real.sqrt (Real.pi / β) : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_exp]
    rw [integral_complex_ofReal, integral_gaussian]
  simpa only [hgauss] using hlim

/-- The horizontal saddle asymptotic for any bounded imaginary family. -/
theorem tendsto_sqrt_mul_horizontalSaddleIntegral
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {β M : ℝ} {A v : ι → ℝ} (hβ : 0 < β)
    (hA : Tendsto A l atTop) (hv : ∀ᶠ i in l, |v i| ≤ M) :
    Tendsto (fun i => (Real.sqrt (A i) : ℂ) *
      horizontalSaddleIntegral β ((A i : ℂ) + (v i : ℂ) * Complex.I)) l
      (𝓝 ((Real.sqrt (Real.pi / β) : ℝ) : ℂ)) := by
  apply (tendsto_integral_scaledHorizontalSaddle hβ hA hv).congr'
  filter_upwards [hA.eventually (eventually_gt_atTop (0 : ℝ))] with i hi
  exact integral_scaledHorizontalSaddle_eq hi

/-- An interface directly applicable to complex critical points, including Lambert roots. -/
theorem tendsto_sqrt_re_mul_horizontalSaddleIntegral
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {β M : ℝ} {w : ι → ℂ} (hβ : 0 < β)
    (hre : Tendsto (fun i => (w i).re) l atTop)
    (him : ∀ᶠ i in l, |(w i).im| ≤ M) :
    Tendsto (fun i => (Real.sqrt (w i).re : ℂ) * horizontalSaddleIntegral β (w i)) l
      (𝓝 ((Real.sqrt (Real.pi / β) : ℝ) : ℂ)) := by
  simpa only [Complex.re_add_im] using tendsto_sqrt_mul_horizontalSaddleIntegral hβ hre him

/-- The leading coefficient is positive, so the horizontal integral eventually is nonzero. -/
theorem eventually_horizontalSaddleIntegral_ne_zero
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {β M : ℝ} {w : ι → ℂ} (hβ : 0 < β)
    (hre : Tendsto (fun i => (w i).re) l atTop)
    (him : ∀ᶠ i in l, |(w i).im| ≤ M) :
    ∀ᶠ i in l, horizontalSaddleIntegral β (w i) ≠ 0 := by
  have hc : ((Real.sqrt (Real.pi / β) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hβ)).ne'
  filter_upwards [(tendsto_sqrt_re_mul_horizontalSaddleIntegral hβ hre him).eventually_ne hc]
    with i hi
  intro hz
  exact hi (by rw [hz, mul_zero])

end InfiniteZero
