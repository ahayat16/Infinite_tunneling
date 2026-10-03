import InfiniteZero.MagneticIntegrationByParts

/-!
Local integration by parts: only the first factor needs compact support.
This lets the differential eigenvalue equation be tested against compact
cutoffs without assuming any global energy integral for the eigenfunction.
-/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace InfiniteZero

/-- Integration by parts for the actual coordinate derivative with compact first argument and smooth second argument. -/
theorem waveInner_partialDerivative_smooth_right (i : Fin 2) {ψ χ : Wavefunction}
    (hψ : IsTestFunction ψ) (hχ : ContDiff ℝ ∞ χ) :
    waveInner ψ (partialDerivative i χ) = -waveInner (partialDerivative i ψ) χ := by
  have hf : ∀ x ∈ tsupport χ, DifferentiableAt ℝ (fun y => star (ψ y)) x :=
    fun x _ => ((hψ.1.differentiable (by simp)) x).star
  have hg : ∀ x ∈ tsupport (fun y => star (ψ y)), DifferentiableAt ℝ χ x :=
    fun x _ => (hχ.differentiable (by simp)) x
  have hleft := (hψ.partialDerivative i).integrable_star_mul hχ.continuous
  have hright := hψ.integrable_star_mul (contDiff_partialDerivative i hχ).continuous
  have hzero := hψ.integrable_star_mul hχ.continuous
  simpa only [waveInner, partialDerivative, fderiv_star,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply] using
    (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := coordinateVector i) (by simpa only [fderiv_star,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply] using hleft)
      hright hzero hf hg)

/-- Each concrete magnetic momentum is symmetric against a smooth function with a compact first argument. -/
theorem waveInner_covariantDerivative_smooth_right (b coupling : ℝ) (i : Fin 2)
    {ψ χ : Wavefunction} (hψ : IsTestFunction ψ) (hχ : ContDiff ℝ ∞ χ) :
    waveInner ψ (covariantDerivative b coupling i χ) =
      waveInner (covariantDerivative b coupling i ψ) χ := by
  let a : Plane → ℂ := fun x => ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ)
  have ha : Continuous a := Complex.continuous_ofReal.comp
    (continuous_const.mul (contDiff_perpCoordinate i).continuous)
  have hd := hψ.integrable_star_mul (contDiff_partialDerivative i hχ).continuous
  have hd' := (hψ.partialDerivative i).integrable_star_mul hχ.continuous
  have hv := hψ.integrable_star_mul (ha.mul hχ.continuous)
  change Integrable (fun x => star (ψ x) * (a x * χ x)) at hv
  have hfirst : waveInner ψ (covariantDerivative b coupling i χ) =
      -Complex.I * waveInner ψ (partialDerivative i χ) -
        ∫ x, star (ψ x) * (a x * χ x) := by
    unfold waveInner covariantDerivative
    simp_rw [mul_sub, show ∀ x : Plane, star (ψ x) * (-Complex.I * partialDerivative i χ x) =
      -Complex.I * (star (ψ x) * partialDerivative i χ x) by intro x; ring]
    rw [integral_sub (hd.const_mul (-Complex.I)) hv, integral_const_mul]
  have hsecond : waveInner (covariantDerivative b coupling i ψ) χ =
      Complex.I * waveInner (partialDerivative i ψ) χ -
        ∫ x, star (ψ x) * (a x * χ x) := by
    unfold waveInner
    have hid : (fun x => star (covariantDerivative b coupling i ψ x) * χ x) =
        fun x => Complex.I * (star (partialDerivative i ψ x) * χ x) -
          star (ψ x) * (a x * χ x) := by
      funext x
      simp only [covariantDerivative, star_sub, star_mul, star_neg, Complex.star_def,
        Complex.conj_I, neg_neg, Complex.conj_ofReal, a]
      ring
    rw [hid, integral_sub (hd'.const_mul Complex.I) hv, integral_const_mul]
  rw [hfirst, hsecond, waveInner_partialDerivative_smooth_right i hψ hχ]
  ring


end InfiniteZero
