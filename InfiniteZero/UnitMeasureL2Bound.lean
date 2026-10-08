import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A Cauchy–Schwarz estimate on a set of unit measure

The elementary variance identity bounds the square of an integral by
the integral of the squared norm when the total measure is one.
-/

noncomputable section
open Set MeasureTheory
namespace InfiniteZero

/-- Integral Cauchy–Schwarz against the constant function one. -/
theorem norm_integral_sq_le_integral_norm_sq_of_measure_univ_eq_one
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} (hμ : μ Set.univ = 1) {f : X → E}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  letI : IsFiniteMeasure μ := ⟨by rw [hμ]; exact ENNReal.one_lt_top⟩
  let m : ℝ := ∫ x, ‖f x‖ ∂μ
  have hm : 0 ≤ m := integral_nonneg fun x => norm_nonneg (f x)
  have hc : Integrable (fun _ : X => m ^ 2) μ := integrable_const _
  have hi : Integrable (fun x => ‖f x‖ ^ 2 - 2 * m * ‖f x‖) μ :=
    hf2.sub (hf.norm.const_mul (2 * m))
  have hvar : 0 ≤ ∫ x, (‖f x‖ ^ 2 - 2 * m * ‖f x‖) + m ^ 2 ∂μ :=
    integral_nonneg fun x => by
      change (0 : ℝ) ≤ ‖f x‖ ^ 2 - 2 * m * ‖f x‖ + m ^ 2
      nlinarith [sq_nonneg (‖f x‖ - m)]
  rw [integral_add hi hc, integral_sub hf2 (hf.norm.const_mul (2 * m)),
    integral_const_mul, integral_const] at hvar
  have hμr : μ.real Set.univ = 1 := by simp [Measure.real, hμ]
  rw [hμr, one_smul] at hvar
  have hn := norm_integral_le_integral_norm (μ := μ) f
  change ‖∫ x, f x ∂μ‖ ≤ m at hn
  change 0 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) - 2 * m * m + m ^ 2 at hvar
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]

end InfiniteZero
