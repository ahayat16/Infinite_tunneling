import InfiniteZero.MagneticAgmonWeighted

/-! Product identities for the spatial cutoffs used to remove localization. -/

noncomputable section
namespace InfiniteZero

theorem realPartialDerivative_mul (i : Fin 2) {σ χ : Plane → ℝ} {x : Plane}
    (hσ : DifferentiableAt ℝ σ x) (hχ : DifferentiableAt ℝ χ x) :
    realPartialDerivative i (fun y => σ y * χ y) x =
      χ x * realPartialDerivative i σ x + σ x * realPartialDerivative i χ x := by
  have hd := hσ.hasFDerivAt.mul hχ.hasFDerivAt
  have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (coordinateVector i)) hd.fderiv
  simpa only [realPartialDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, add_comm] using he

theorem cutoffGradientSq_mul_le {σ χ : Plane → ℝ} {x : Plane}
    (hσ : DifferentiableAt ℝ σ x) (hχ : DifferentiableAt ℝ χ x) :
    cutoffGradientSq (fun y => σ y * χ y) x ≤
      2 * χ x ^ 2 * cutoffGradientSq σ x + 2 * σ x ^ 2 * cutoffGradientSq χ x := by
  simp only [cutoffGradientSq, realPartialDerivative_mul _ hσ hχ,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (χ x * realPartialDerivative i σ x -
    σ x * realPartialDerivative i χ x)]

theorem cutoffGradientSq_mul_eq_of_one {σ χ : Plane → ℝ} {x : Plane}
    (hσ : DifferentiableAt ℝ σ x) (hχ : DifferentiableAt ℝ χ x)
    (hone : χ x = 1) (hzero : ∀ i, realPartialDerivative i χ x = 0) :
    cutoffGradientSq (fun y => σ y * χ y) x = cutoffGradientSq σ x := by
  simp only [cutoffGradientSq, realPartialDerivative_mul _ hσ hχ, hone, hzero,
    one_mul, mul_zero, add_zero]

end InfiniteZero
