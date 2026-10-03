import InfiniteZero.MagneticLocalEnergy

/-!
# Local forbidden-region estimates

These inequalities apply to the actual differential eigenfunction and its
actual compact cutoffs. No global energy integral, Agmon estimate, or weighted
inverse is assumed. They provide the energy estimate needed before choosing
and removing the cutoffs in a global exponential-decay argument.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InfiniteZero

theorem cutoff_mass_le_gradient_error {b coupling E δ : ℝ} {V : Potential}
    {χ : Plane → ℝ} {φ : Wavefunction} (hV : Continuous V)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hφ : IsEigenfunction b coupling V E φ)
    (hreserve : ∀ x, χ x ≠ 0 → δ ≤ coupling ^ 2 * V x - E) :
    δ * mass (fun x => (χ x : ℂ) * φ x) ≤
      ∫ x : Plane, cutoffGradientSq χ x * ‖φ x‖ ^ 2 := by
  let ψ : Wavefunction := fun x => (χ x : ℂ) * φ x
  have ht : IsTestFunction ψ := isTestFunction_compact_real_mul hχ hc hφ.1
  have hn := ht.integrable_norm_sq
  have hd := ht.integrable_magneticEnergyDensity b coupling hV
  have hbound (x : Plane) :
      δ * ‖ψ x‖ ^ 2 ≤ magneticEnergyDensity b coupling V ψ x - E * ‖ψ x‖ ^ 2 := by
    have hp : δ * ‖ψ x‖ ^ 2 ≤ (coupling ^ 2 * V x - E) * ‖ψ x‖ ^ 2 := by
      by_cases hx : χ x = 0
      · simp [ψ, hx]
      · exact mul_le_mul_of_nonneg_right (hreserve x hx) (sq_nonneg _)
    have hk : 0 ≤ ∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    dsimp only [magneticEnergyDensity]
    nlinarith only [hp, hk]
  calc
    _ = ∫ x : Plane, δ * ‖ψ x‖ ^ 2 := (integral_const_mul _ _).symm
    _ ≤ ∫ x : Plane, magneticEnergyDensity b coupling V ψ x - E * ‖ψ x‖ ^ 2 :=
      integral_mono (hn.const_mul δ) (hd.sub (hn.const_mul E)) hbound
    _ = magneticForm b coupling V ψ - E * mass ψ := by
      rw [integral_sub hd (hn.const_mul E), integral_const_mul]
      rfl
    _ = _ := magneticForm_cutoff_eigenfunction hV hχ hc hφ

theorem realPartialDerivative_mul_exp (i : Fin 2) {η F : Plane → ℝ} {x : Plane}
    (hη : DifferentiableAt ℝ η x) (hF : DifferentiableAt ℝ F x) :
    realPartialDerivative i (fun y => η y * Real.exp (F y)) x =
      Real.exp (F x) * (realPartialDerivative i η x + η x * realPartialDerivative i F x) := by
  have hd := hη.hasFDerivAt.mul hF.hasFDerivAt.exp
  have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (coordinateVector i)) hd.fderiv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at he
  simpa only [realPartialDerivative, mul_add, mul_assoc, mul_left_comm, mul_comm,
    add_comm] using he

theorem cutoffGradientSq_mul_exp_le {η F : Plane → ℝ} {x : Plane}
    (hη : DifferentiableAt ℝ η x) (hF : DifferentiableAt ℝ F x) :
    cutoffGradientSq (fun y => η y * Real.exp (F y)) x ≤
      2 * Real.exp (F x) ^ 2 * cutoffGradientSq η x +
      2 * (η x * Real.exp (F x)) ^ 2 * cutoffGradientSq F x := by
  simp only [cutoffGradientSq, realPartialDerivative_mul_exp _ hη hF,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hs : (realPartialDerivative i η x + η x * realPartialDerivative i F x) ^ 2 ≤
      2 * realPartialDerivative i η x ^ 2 + 2 * (η x * realPartialDerivative i F x) ^ 2 := by
    nlinarith [sq_nonneg (realPartialDerivative i η x - η x * realPartialDerivative i F x)]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.exp (F x)))
  nlinarith only [hm]

end InfiniteZero
