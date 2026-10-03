import InfiniteZero.MagneticAgmonWeighted

/-!
# The exact weighted magnetic pairing on the test core

Only the test function is compactly supported. The real smooth weight may
be noncompact. This identity allows a weighted inequality to be expressed
solely in terms of a test graph pair before passing to the closed graph.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InfiniteZero

theorem IsTestFunction.integrable_real_mul_norm_sq {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) {P : Plane → ℝ} (hP : Continuous P) :
    Integrable (fun x => P x * ‖ψ x‖ ^ 2) := by
  apply (hP.mul (hψ.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  exact (hψ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mul_left

theorem magneticForm_real_mul_test (b coupling : ℝ) {V : Potential}
    {χ : Plane → ℝ} {ψ : Wavefunction} (hV : Continuous V)
    (hχ : ContDiff ℝ ∞ χ) (hψ : IsTestFunction ψ) :
    magneticForm b coupling V (fun x => (χ x : ℂ) * ψ x) =
      (waveInner (fun x => ((χ x ^ 2 : ℝ) : ℂ) * ψ x)
        (magneticHamiltonian b coupling V ψ)).re +
      ∫ x : Plane, cutoffGradientSq χ x * ‖ψ x‖ ^ 2 := by
  have htest := hψ.real_mul (hχ.pow 2)
  have hmixed := integrable_magneticMixedDensity b coupling hV htest hψ.1
  have hmixedRe : Integrable (fun x =>
      (magneticMixedDensity b coupling V (fun y => ((χ y ^ 2 : ℝ) : ℂ) * ψ y) ψ x).re) :=
    hmixed.re
  have herr := hψ.integrable_real_mul_norm_sq (continuous_cutoffGradientSq hχ)
  calc
    _ = ∫ x : Plane,
        (magneticMixedDensity b coupling V (fun y => ((χ y ^ 2 : ℝ) : ℂ) * ψ y) ψ x).re +
          cutoffGradientSq χ x * ‖ψ x‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => magneticEnergyDensity_cutoff b coupling V
        ((hχ.differentiable (by simp)) x) ((hψ.1.differentiable (by simp)) x)
    _ = _ := by
      rw [integral_add hmixedRe herr]
      congr 1
      exact (integral_re hmixed).trans (congrArg Complex.re
        (waveInner_magneticHamiltonian_eq_integral_mixed b coupling hV htest hψ.1).symm)

theorem realPartialDerivative_exp (i : Fin 2) {F : Plane → ℝ} {x : Plane}
    (hF : DifferentiableAt ℝ F x) :
    realPartialDerivative i (fun y => Real.exp (F y)) x =
      Real.exp (F x) * realPartialDerivative i F x := by
  have h := congrArg (fun f : Plane →L[ℝ] ℝ => f (coordinateVector i))
    hF.hasFDerivAt.exp.fderiv
  simpa only [realPartialDerivative, ContinuousLinearMap.smul_apply, smul_eq_mul] using h

theorem cutoffGradientSq_exp {F : Plane → ℝ} {x : Plane}
    (hF : DifferentiableAt ℝ F x) :
    cutoffGradientSq (fun y => Real.exp (F y)) x =
      Real.exp (F x) ^ 2 * cutoffGradientSq F x := by
  simp only [cutoffGradientSq, realPartialDerivative_exp _ hF, mul_pow, Finset.mul_sum]

/-- Exact real pairing; the gradient correction appears with coefficient one. -/
theorem magneticForm_exp_test (b coupling : ℝ) {V : Potential}
    {F : Plane → ℝ} {ψ : Wavefunction} (hV : Continuous V)
    (hF : ContDiff ℝ ∞ F) (hψ : IsTestFunction ψ) :
    magneticForm b coupling V (fun x => (Real.exp (F x) : ℂ) * ψ x) -
      (∫ x : Plane, cutoffGradientSq F x *
        ‖(Real.exp (F x) : ℂ) * ψ x‖ ^ 2) =
      (waveInner (fun x => (Real.exp (F x) : ℂ) * ψ x)
        (fun x => (Real.exp (F x) : ℂ) * magneticHamiltonian b coupling V ψ x)).re := by
  rw [magneticForm_real_mul_test b coupling hV hF.exp hψ]
  have herror : (∫ x : Plane, cutoffGradientSq (fun y => Real.exp (F y)) x * ‖ψ x‖ ^ 2) =
      ∫ x : Plane, cutoffGradientSq F x * ‖(Real.exp (F x) : ℂ) * ψ x‖ ^ 2 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [cutoffGradientSq_exp ((hF.differentiable (by simp)) x)]
      simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
  rw [herror, add_sub_cancel_right]
  congr 1
  unfold waveInner
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [star_mul, Complex.star_def, Complex.ofReal_pow, map_pow, Complex.conj_ofReal]
    ring

end InfiniteZero
