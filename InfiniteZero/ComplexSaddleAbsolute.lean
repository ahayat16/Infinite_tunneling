import InfiniteZero.ComplexLogFlatCutoffAsymptotic
import InfiniteZero.ComplexSaddleLeading

/-!
# Uniform absolute bound on the full complex saddle line

The bound follows from the integrable scaled majorant, and is independent
of the imaginary part of the saddle. It also bounds the original phase on
the full horizontal line through its constructed critical point after the
actual saddle normalization.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

def horizontalSaddleAbsoluteConstant (β : ℝ) : ℝ :=
  1 + ∫ x : ℝ, Real.exp (-(β * Real.exp (-1)) * min (x ^ 2) |x|)

theorem horizontalSaddleAbsoluteConstant_pos (β : ℝ) :
    0 < horizontalSaddleAbsoluteConstant β := by
  unfold horizontalSaddleAbsoluteConstant
  have h : 0 ≤ ∫ x : ℝ, Real.exp (-(β * Real.exp (-1)) * min (x ^ 2) |x|) :=
    integral_nonneg (fun x : ℝ => (Real.exp_pos
      (-(β * Real.exp (-1)) * min (x ^ 2) |x|)).le)
  linarith

theorem integral_norm_scaledHorizontalSaddle_eq {β A v : ℝ} (hA : 0 < A) :
    (∫ x : ℝ, ‖scaledHorizontalSaddle β A v x‖) =
      Real.sqrt A * ∫ q : ℝ,
        ‖Complex.exp (-horizontalSaddlePhase β ((A : ℂ) + (v : ℂ) * Complex.I) q)‖ := by
  unfold scaledHorizontalSaddle
  simp only [div_eq_mul_inv]
  rw [Measure.integral_comp_mul_right
    (fun q : ℝ => ‖Complex.exp (-horizontalSaddlePhase β ((A : ℂ) + (v : ℂ) * Complex.I) q)‖)
    (Real.sqrt A)⁻¹]
  rw [inv_inv, abs_of_pos (Real.sqrt_pos.2 hA)]
  rfl

/-- The normalized absolute integral is uniformly bounded for every imaginary
part, as soon as the real part of the saddle is at least one. -/
theorem sqrt_re_mul_integral_norm_horizontalSaddle_le {β : ℝ} (hβ : 0 < β)
    {w : ℂ} (hw : 1 ≤ w.re) :
    Real.sqrt w.re * (∫ q : ℝ, ‖Complex.exp (-horizontalSaddlePhase β w q)‖) ≤
      horizontalSaddleAbsoluteConstant β := by
  have hmajor := integrable_exp_neg_mul_min_sq_abs (mul_pos hβ (Real.exp_pos (-1)))
  have hscaled : Integrable (fun x : ℝ => ‖scaledHorizontalSaddle β w.re w.im x‖) := by
    apply hmajor.mono' (continuous_scaledHorizontalSaddle β w.re w.im).norm.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      simpa only [norm_norm] using norm_scaledHorizontalSaddle_le hβ.le hw w.im x)
  have he := integral_norm_scaledHorizontalSaddle_eq
    (β := β) (v := w.im) (show 0 < w.re by linarith)
  rw [Complex.re_add_im] at he
  rw [← he]
  calc
    _ ≤ ∫ x : ℝ, Real.exp (-(β * Real.exp (-1)) * min (x ^ 2) |x|) :=
      integral_mono hscaled hmajor (norm_scaledHorizontalSaddle_le hβ.le hw w.im)
    _ ≤ horizontalSaddleAbsoluteConstant β := by
      unfold horizontalSaddleAbsoluteConstant
      linarith

theorem exists_uniform_absolute_horizontalSaddle_bound {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 1 ≤ w.re →
      Real.sqrt w.re * (∫ q : ℝ, ‖Complex.exp (-horizontalSaddlePhase β w q)‖) ≤ C :=
  ⟨horizontalSaddleAbsoluteConstant β, horizontalSaddleAbsoluteConstant_pos β,
    fun _ hw => sqrt_re_mul_integral_norm_horizontalSaddle_le hβ hw⟩

theorem logFlatComplexPhase_saddle_add {β k : ℝ} (hβ : β ≠ 0) {C w : ℂ}
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w) (q : ℝ) :
    logFlatComplexPhase β k C (logFlatComplexCritical β k w + (q : ℂ)) =
      logFlatComplexPhase β k C (logFlatComplexCritical β k w) +
        horizontalSaddlePhase β w q := by
  have hd := logFlatComplexPhase_difference hβ hc (q : ℂ)
  have hp : (β : ℂ) * (q : ℂ) ^ 2 + 2 * (β : ℂ) * w *
      (Complex.exp (-(q : ℂ)) - 1 + (q : ℂ)) = horizontalSaddlePhase β w q := by
    simp [horizontalSaddlePhase, exponentialRemainder, Complex.ofReal_exp]
  rw [hp] at hd
  linear_combination hd

theorem integrable_exp_neg_logFlatComplexPhase_saddle {β k : ℝ} (hβ : 0 < β)
    {C w : ℂ} (hw : 0 ≤ w.re)
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w) :
    Integrable (fun q : ℝ => Complex.exp (-logFlatComplexPhase β k C
      (logFlatComplexCritical β k w + (q : ℂ)))) := by
  simp_rw [logFlatComplexPhase_saddle_add hβ.ne' hc, neg_add, Complex.exp_add]
  exact (integrable_exp_neg_horizontalSaddlePhase hβ hw).const_mul _

/-- Exact cancellation of the possibly large critical exponential inside the
normalized absolute contour integral. -/
theorem norm_saddleNormalizer_mul_integral_norm_eq {β k : ℝ} (hβ : β ≠ 0) {C w : ℂ}
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w) :
    ‖(Real.sqrt w.re : ℂ) *
        Complex.exp (logFlatComplexPhase β k C (logFlatComplexCritical β k w))‖ *
      (∫ q : ℝ, ‖Complex.exp (-logFlatComplexPhase β k C
        (logFlatComplexCritical β k w + (q : ℂ)))‖) =
      Real.sqrt w.re * ∫ q : ℝ, ‖Complex.exp (-horizontalSaddlePhase β w q)‖ := by
  simp_rw [logFlatComplexPhase_saddle_add hβ hc, neg_add, Complex.exp_add, norm_mul]
  rw [integral_const_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have he : ‖Complex.exp (logFlatComplexPhase β k C (logFlatComplexCritical β k w))‖ *
      ‖Complex.exp (-logFlatComplexPhase β k C (logFlatComplexCritical β k w))‖ = 1 := by
    rw [← norm_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, norm_one]
  calc
    _ = Real.sqrt w.re *
        (‖Complex.exp (logFlatComplexPhase β k C (logFlatComplexCritical β k w))‖ *
          ‖Complex.exp (-logFlatComplexPhase β k C (logFlatComplexCritical β k w))‖) *
        (∫ q : ℝ, ‖Complex.exp (-horizontalSaddlePhase β w q)‖) := by ring
    _ = _ := by rw [he, mul_one]

/-- The actual constructed saddle satisfies the absolute contour estimate;
the constant depends only on `β`. -/
theorem eventually_logFlatSaddle_absolute_bound {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖logFlatSaddleNormalizer β k tStar c h‖ *
        (∫ q : ℝ, ‖Complex.exp (-logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
          (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h) + (q : ℂ)))‖) ≤
        horizontalSaddleAbsoluteConstant β := by
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc,
    eventually_logFlatSaddleRoot_critical (k := k) hβ.ne' ht.ne' hc] with h hw hcrit
  unfold logFlatSaddleNormalizer
  rw [norm_saddleNormalizer_mul_integral_norm_eq hβ.ne' hcrit.1]
  exact sqrt_re_mul_integral_norm_horizontalSaddle_le hβ (by linarith [hw.1])

theorem eventually_integrable_logFlatSaddleHorizontal {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun q : ℝ =>
      Complex.exp (-logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h) + (q : ℂ)))) := by
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc,
    eventually_logFlatSaddleRoot_critical (k := k) hβ.ne' ht.ne' hc] with h hw hcrit
  exact integrable_exp_neg_logFlatComplexPhase_saddle hβ (by linarith [hw.1]) hcrit.1

/-- A uniform multiplier error can be inserted under a normalized complex
integral using an absolute integral bound. The measure can be restricted to
any measurable contour parameter domain. -/
theorem norm_normalized_integral_sub_le_of_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f B : X → ℂ} {B₀ N : ℂ} {ε C : ℝ}
    (hf : Integrable f μ) (hB : Integrable (fun q => f q * B q) μ)
    (hε : 0 ≤ ε) (herr : ∀ᵐ q ∂μ, ‖B q - B₀‖ ≤ ε)
    (hC : ‖N‖ * (∫ q, ‖f q‖ ∂μ) ≤ C) :
    ‖N * ((∫ q, f q * B q ∂μ) - B₀ * ∫ q, f q ∂μ)‖ ≤ C * ε := by
  have he : (∫ q, f q * B q ∂μ) - B₀ * (∫ q, f q ∂μ) =
      ∫ q, f q * (B q - B₀) ∂μ := by
    rw [← integral_const_mul, ← integral_sub hB (hf.const_mul B₀)]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by ring
  have hi : ‖∫ q, f q * (B q - B₀) ∂μ‖ ≤ ε * ∫ q, ‖f q‖ ∂μ := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hf.norm.const_mul ε)
    filter_upwards [herr] with q hq
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hq (norm_nonneg _)).trans_eq (mul_comm _ _)
  rw [he, norm_mul]
  calc
    _ ≤ ‖N‖ * (ε * ∫ q, ‖f q‖ ∂μ) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = (‖N‖ * ∫ q, ‖f q‖ ∂μ) * ε := by ring
    _ ≤ C * ε := mul_le_mul_of_nonneg_right hC hε

end InfiniteZero
