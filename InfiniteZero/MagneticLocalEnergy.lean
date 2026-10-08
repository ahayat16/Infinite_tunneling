import InfiniteZero.MagneticIntegrationByPartsLocal

/-!
# Local energy identity for actual smooth eigenfunctions

Compact real cutoffs turn a possibly noncompact eigenfunction into a test
function. All integrations by parts are local; no global form-domain or
energy-integrability assumption is used for the eigenfunction.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InfiniteZero

theorem isTestFunction_compact_real_mul {χ : Plane → ℝ} {φ : Wavefunction}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hφ : ContDiff ℝ ∞ φ) :
    IsTestFunction (fun x => (χ x : ℂ) * φ x) :=
  ⟨(Complex.ofRealCLM.contDiff.comp hχ).mul hφ,
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right⟩

def magneticMixedDensity (b coupling : ℝ) (V : Potential)
    (ψ φ : Wavefunction) (x : Plane) : ℂ :=
  (∑ i : Fin 2, star (covariantDerivative b coupling i ψ x) *
    covariantDerivative b coupling i φ x) +
    star (ψ x) * (((coupling ^ 2 * V x : ℝ) : ℂ) * φ x)

theorem integrable_magneticMixedDensity (b coupling : ℝ) {V : Potential}
    {ψ φ : Wavefunction} (hV : Continuous V) (hψ : IsTestFunction ψ)
    (hφ : ContDiff ℝ ∞ φ) : Integrable (magneticMixedDensity b coupling V ψ φ) := by
  apply Integrable.add
  · exact integrable_finsetSum Finset.univ fun i _ =>
      (hψ.covariantDerivative b coupling i).integrable_star_mul
        (contDiff_covariantDerivative b coupling i hφ).continuous
  · exact hψ.integrable_star_mul
      ((Complex.continuous_ofReal.comp (continuous_const.mul hV)).mul hφ.continuous)

theorem waveInner_magneticHamiltonian_eq_integral_mixed (b coupling : ℝ)
    {V : Potential} {ψ φ : Wavefunction} (hV : Continuous V)
    (hψ : IsTestFunction ψ) (hφ : ContDiff ℝ ∞ φ) :
    waveInner ψ (magneticHamiltonian b coupling V φ) =
      ∫ x : Plane, magneticMixedDensity b coupling V ψ φ x := by
  have hkin (i : Fin 2) := hψ.integrable_star_mul
    (contDiff_covariantDerivative b coupling i
      (contDiff_covariantDerivative b coupling i hφ)).continuous
  have hmixed (i : Fin 2) := (hψ.covariantDerivative b coupling i).integrable_star_mul
    (contDiff_covariantDerivative b coupling i hφ).continuous
  have hpot : Integrable (fun x => star (ψ x) *
      (((coupling ^ 2 * V x : ℝ) : ℂ) * φ x)) := hψ.integrable_star_mul
    ((Complex.continuous_ofReal.comp (continuous_const.mul hV)).mul hφ.continuous)
  unfold waveInner magneticHamiltonian magneticMixedDensity
  simp_rw [mul_add, Finset.mul_sum]
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hkin i)) hpot,
    integral_add (integrable_finsetSum Finset.univ (fun i _ => hmixed i)) hpot,
    integral_finsetSum Finset.univ (fun i _ => hkin i),
    integral_finsetSum Finset.univ (fun i _ => hmixed i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact waveInner_covariantDerivative_smooth_right b coupling i hψ
    (contDiff_covariantDerivative b coupling i hφ)

theorem realPartialDerivative_sq (i : Fin 2) {χ : Plane → ℝ} {x : Plane}
    (hχ : DifferentiableAt ℝ χ x) :
    realPartialDerivative i (fun y => χ y ^ 2) x =
      2 * χ x * realPartialDerivative i χ x := by
  have hd := hχ.hasFDerivAt.mul hχ.hasFDerivAt
  have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (coordinateVector i)) hd.fderiv
  simpa only [realPartialDerivative, pow_two, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, two_mul, add_mul] using he

def cutoffGradientSq (χ : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, realPartialDerivative i χ x ^ 2

theorem cutoffGradientSq_nonneg (χ : Plane → ℝ) (x : Plane) :
    0 ≤ cutoffGradientSq χ x := Finset.sum_nonneg fun i _ =>
      sq_nonneg (realPartialDerivative i χ x)

private theorem complex_local_energy (c a : ℝ) (z v : ℂ) :
    ‖(c : ℂ) * z - Complex.I * (a : ℂ) * v‖ ^ 2 =
      (star (((c ^ 2 : ℝ) : ℂ) * z - Complex.I * ((2 * c * a : ℝ) : ℂ) * v) * z).re +
        a ^ 2 * ‖v‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem magneticEnergyDensity_cutoff (b coupling : ℝ) (V : Potential)
    {χ : Plane → ℝ} {φ : Wavefunction} {x : Plane}
    (hχ : DifferentiableAt ℝ χ x) (hφ : DifferentiableAt ℝ φ x) :
    magneticEnergyDensity b coupling V (fun y => (χ y : ℂ) * φ y) x =
      (magneticMixedDensity b coupling V (fun y => ((χ y ^ 2 : ℝ) : ℂ) * φ y) φ x).re +
        cutoffGradientSq χ x * ‖φ x‖ ^ 2 := by
  have hkin (i : Fin 2) :
      ‖covariantDerivative b coupling i (fun y => (χ y : ℂ) * φ y) x‖ ^ 2 =
      (star (covariantDerivative b coupling i
        (fun y => ((χ y ^ 2 : ℝ) : ℂ) * φ y) x) * covariantDerivative b coupling i φ x).re +
        realPartialDerivative i χ x ^ 2 * ‖φ x‖ ^ 2 := by
    rw [covariantDerivative_real_mul b coupling i hχ hφ,
      covariantDerivative_real_mul b coupling i
        (χ := fun y => χ y ^ 2) (hχ.pow 2) hφ,
      realPartialDerivative_sq i hχ]
    exact complex_local_energy _ _ _ _
  simp only [magneticEnergyDensity, magneticMixedDensity, cutoffGradientSq,
    Complex.add_re, Complex.re_sum, hkin, Finset.sum_add_distrib, Finset.sum_mul]
  have hp : coupling ^ 2 * V x * ‖(χ x : ℂ) * φ x‖ ^ 2 =
      (star (((χ x ^ 2 : ℝ) : ℂ) * φ x) * (((coupling ^ 2 * V x : ℝ) : ℂ) * φ x)).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hp]
  ring

theorem integrable_cutoffGradientSq_mul {χ : Plane → ℝ} {φ : Wavefunction}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hφ : Continuous φ) :
    Integrable (fun x => cutoffGradientSq χ x * ‖φ x‖ ^ 2) := by
  simp_rw [cutoffGradientSq, Finset.sum_mul]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply (((contDiff_realPartialDerivative i hχ).continuous.pow 2).mul
    (hφ.norm.pow 2)).integrable_of_hasCompactSupport
  exact ((hc.fderiv_apply ℝ (coordinateVector i)).comp_left
    (g := fun r : ℝ => r ^ 2) (by simp)).mul_right

/-- The localized energy is the equation tested against the squared cutoff,
plus the explicit squared-gradient error. The second function need not be
compactly supported or have globally integrable derivatives. -/
theorem magneticForm_cutoff (b coupling : ℝ) {V : Potential}
    {χ : Plane → ℝ} {φ : Wavefunction} (hV : Continuous V)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hφ : ContDiff ℝ ∞ φ) :
    magneticForm b coupling V (fun x => (χ x : ℂ) * φ x) =
      (waveInner (fun x => ((χ x ^ 2 : ℝ) : ℂ) * φ x)
        (magneticHamiltonian b coupling V φ)).re +
      ∫ x : Plane, cutoffGradientSq χ x * ‖φ x‖ ^ 2 := by
  have htest := isTestFunction_compact_real_mul (χ := fun x => χ x ^ 2)
    (hχ.pow 2) (hc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)) hφ
  have hmixed := integrable_magneticMixedDensity b coupling hV htest hφ
  have hmixedRe : Integrable (fun x =>
      (magneticMixedDensity b coupling V (fun y => ((χ y ^ 2 : ℝ) : ℂ) * φ y) φ x).re) :=
    hmixed.re
  have herr := integrable_cutoffGradientSq_mul hχ hc hφ.continuous
  calc
    _ = ∫ x : Plane,
        (magneticMixedDensity b coupling V (fun y => ((χ y ^ 2 : ℝ) : ℂ) * φ y) φ x).re +
          cutoffGradientSq χ x * ‖φ x‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => magneticEnergyDensity_cutoff b coupling V
        ((hχ.differentiable (by simp)) x) ((hφ.differentiable (by simp)) x)
    _ = _ := by
      rw [integral_add hmixedRe herr]
      congr 1
      exact (integral_re hmixed).trans (congrArg Complex.re
        (waveInner_magneticHamiltonian_eq_integral_mixed b coupling hV htest hφ).symm)

/-- Localized eigenfunction identity, the starting point for weighted Agmon
estimates. All integrability assumptions are consequences of the compact
cutoff; no realization or spectral admission is used in this theorem. -/
theorem magneticForm_cutoff_eigenfunction {b coupling E : ℝ} {V : Potential}
    {χ : Plane → ℝ} {φ : Wavefunction} (hV : Continuous V)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hφ : IsEigenfunction b coupling V E φ) :
    magneticForm b coupling V (fun x => (χ x : ℂ) * φ x) -
      E * mass (fun x => (χ x : ℂ) * φ x) =
      ∫ x : Plane, cutoffGradientSq χ x * ‖φ x‖ ^ 2 := by
  rw [magneticForm_cutoff b coupling hV hχ hc hφ.1]
  have hi : waveInner (fun x => ((χ x ^ 2 : ℝ) : ℂ) * φ x)
      (magneticHamiltonian b coupling V φ) =
      ((E * mass (fun x => (χ x : ℂ) * φ x) : ℝ) : ℂ) := by
    have hf : (fun x => star (((χ x ^ 2 : ℝ) : ℂ) * φ x) *
        magneticHamiltonian b coupling V φ x) =
        fun x => ((E * ‖(χ x : ℂ) * φ x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      rw [hφ.2.2 x]
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal, norm_mul,
        mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_mul]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      ring
    unfold waveInner mass
    rw [hf, integral_complex_ofReal, integral_const_mul]
  rw [hi, Complex.ofReal_re]
  ring

end InfiniteZero
