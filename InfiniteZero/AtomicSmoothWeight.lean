import InfiniteZero.MagneticWeightedTest
import InfiniteZero.AtomicLocalizationCutoffs

/-!
# Smooth weights vanishing near the core

The gradient cost is supported on the exterior part of the fixed IMS
partition. This is the concrete hypothesis used in the weighted test lower
bound, before any closed-graph or Lipschitz-limit argument.
-/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace InfiniteZero.CuspParameters

theorem cutoffGradientSq_zero_of_core_neighborhood {p : CuspParameters}
    {F : Plane → ℝ} (hzero : ∀ x, ‖x‖ ≤ 4 * p.r₀ → F x = 0)
    {x : Plane} (hx : ‖x‖ < 4 * p.r₀) : cutoffGradientSq F x = 0 := by
  have hevent : ∀ᶠ y in 𝓝 x, ‖y‖ < 4 * p.r₀ :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx
  have hz : F =ᶠ[𝓝 x] fun _ => 0 := hevent.mono fun y hy => hzero y hy.le
  have hf : fderiv ℝ F x = 0 := by
    simpa only [fderiv_const_apply] using hz.fderiv_eq (𝕜 := ℝ)
  simp only [cutoffGradientSq, realPartialDerivative, hf, ContinuousLinearMap.zero_apply,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

theorem cutoffGradientSq_le_atomicOuterCutoff_sq {p : CuspParameters}
    (hr : 0 < p.r₀) {F : Plane → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ x, ‖x‖ ≤ 4 * p.r₀ → F x = 0)
    (hgrad : ∀ x, cutoffGradientSq F x ≤ B) (x : Plane) :
    cutoffGradientSq F x ≤ B * (atomicOuterCutoff p hr x) ^ 2 := by
  by_cases hx : 3 * p.r₀ ≤ ‖x‖
  · rw [atomicOuterCutoff_one hr hx, one_pow, mul_one]
    exact hgrad x
  · have hx' : ‖x‖ < 4 * p.r₀ := by linarith [lt_of_not_ge hx]
    rw [cutoffGradientSq_zero_of_core_neighborhood hzero hx']
    exact mul_nonneg hB (sq_nonneg _)

theorem realPartialDerivative_const_mul (i : Fin 2) (a : ℝ) {F : Plane → ℝ} {x : Plane}
    (hF : DifferentiableAt ℝ F x) :
    realPartialDerivative i (fun y => a * F y) x = a * realPartialDerivative i F x := by
  have h := congrArg (fun f : Plane →L[ℝ] ℝ => f (coordinateVector i))
    (hF.hasFDerivAt.const_mul a).fderiv
  simpa only [realPartialDerivative, ContinuousLinearMap.smul_apply, smul_eq_mul] using h

theorem cutoffGradientSq_const_mul (a : ℝ) {F : Plane → ℝ} {x : Plane}
    (hF : DifferentiableAt ℝ F x) :
    cutoffGradientSq (fun y => a * F y) x = a ^ 2 * cutoffGradientSq F x := by
  simp only [cutoffGradientSq, realPartialDerivative_const_mul _ a hF, mul_pow, Finset.mul_sum]

/-- A fixed gradient bound on a smooth geometric weight supplies the exterior
penalty bound uniformly in the coupling. -/
theorem scaledWeight_gradient_penalty {p : CuspParameters} (hr : 0 < p.r₀)
    {T : Plane → ℝ} (hT : ContDiff ℝ ∞ T) {G κ : ℝ}
    (hzero : ∀ x, ‖x‖ ≤ 4 * p.r₀ → T x = 0)
    (hgrad : ∀ x, cutoffGradientSq T x ≤ G) (hκ : κ ^ 2 * G ≤ 1 / 8)
    (coupling : ℝ) (x : Plane) :
    cutoffGradientSq (fun y => κ * coupling * T y) x ≤
      (coupling ^ 2 / 8) * (atomicOuterCutoff p hr x) ^ 2 := by
  apply cutoffGradientSq_le_atomicOuterCutoff_sq hr
    (div_nonneg (sq_nonneg coupling) (by norm_num))
  · intro y hy
    rw [hzero y hy, mul_zero]
  · intro y
    rw [cutoffGradientSq_const_mul _ ((hT.differentiable (by simp)) y)]
    have h1 := mul_le_mul_of_nonneg_left (hgrad y) (sq_nonneg (κ * coupling))
    have h2 := mul_le_mul_of_nonneg_left hκ (sq_nonneg coupling)
    nlinarith only [h1, h2]

end InfiniteZero.CuspParameters
