import InfiniteZero.MagneticIMSIntegrated
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# The differential magnetic Hamiltonian and its test-function form

Integration by parts for the actual coordinate derivatives proves symmetry of
the covariant momenta. The resulting complex energy identity links the
concrete Hamiltonian to the previously defined integral form. No assertion
about noncompact eigenfunctions or the closed operator domain is made here.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace InfiniteZero

theorem IsTestFunction.partialDerivative {ψ : Wavefunction} (hψ : IsTestFunction ψ)
    (i : Fin 2) : IsTestFunction (partialDerivative i ψ) :=
  ⟨contDiff_partialDerivative i hψ.1, hasCompactSupport_partialDerivative i hψ.2⟩

theorem IsTestFunction.covariantDerivative {ψ : Wavefunction} (hψ : IsTestFunction ψ)
    (b coupling : ℝ) (i : Fin 2) : IsTestFunction (covariantDerivative b coupling i ψ) :=
  ⟨contDiff_covariantDerivative b coupling i hψ.1,
    hasCompactSupport_covariantDerivative b coupling i hψ.2⟩

theorem IsTestFunction.integrable_star_mul {ψ χ : Wavefunction}
    (hψ : IsTestFunction ψ) (hχ : Continuous χ) :
    Integrable (fun x => star (ψ x) * χ x) := by
  apply (hψ.1.continuous.star.mul hχ).integrable_of_hasCompactSupport
  exact (hψ.2.comp_left (g := star) (by simp)).mul_right

/-- Integration by parts for the actual coordinate derivative on test functions. -/
theorem waveInner_partialDerivative (i : Fin 2) {ψ χ : Wavefunction}
    (hψ : IsTestFunction ψ) (hχ : IsTestFunction χ) :
    waveInner ψ (partialDerivative i χ) = -waveInner (partialDerivative i ψ) χ := by
  have hf : ∀ x ∈ tsupport χ, DifferentiableAt ℝ (fun y => star (ψ y)) x :=
    fun x _ => ((hψ.1.differentiable (by simp)) x).star
  have hg : ∀ x ∈ tsupport (fun y => star (ψ y)), DifferentiableAt ℝ χ x :=
    fun x _ => (hχ.1.differentiable (by simp)) x
  have hleft := (hψ.partialDerivative i).integrable_star_mul hχ.1.continuous
  have hright := hψ.integrable_star_mul (hχ.partialDerivative i).1.continuous
  have hzero := hψ.integrable_star_mul hχ.1.continuous
  simpa only [waveInner, partialDerivative, fderiv_star,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply] using
    (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := coordinateVector i) (by simpa only [fderiv_star,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply] using hleft)
      hright hzero hf hg)

/-- Each concrete magnetic momentum is symmetric on smooth compactly supported functions. -/
theorem waveInner_covariantDerivative (b coupling : ℝ) (i : Fin 2)
    {ψ χ : Wavefunction} (hψ : IsTestFunction ψ) (hχ : IsTestFunction χ) :
    waveInner ψ (covariantDerivative b coupling i χ) =
      waveInner (covariantDerivative b coupling i ψ) χ := by
  let a : Plane → ℂ := fun x => ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ)
  have ha : Continuous a := Complex.continuous_ofReal.comp
    (continuous_const.mul (contDiff_perpCoordinate i).continuous)
  have hd := hψ.integrable_star_mul (hχ.partialDerivative i).1.continuous
  have hd' := (hψ.partialDerivative i).integrable_star_mul hχ.1.continuous
  have hv := hψ.integrable_star_mul (ha.mul hχ.1.continuous)
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
  rw [hfirst, hsecond, waveInner_partialDerivative i hψ hχ]
  ring

/-- The scalar inner product of a function with itself is its real mass. -/
theorem waveInner_self_eq_mass (ψ : Wavefunction) :
    waveInner ψ ψ = (mass ψ : ℂ) := by
  simp only [waveInner, mass, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  exact integral_complex_ofReal

/-- On the test-function core, the differential Hamiltonian gives exactly the
quadratic form. Continuity of the potential suffices. -/
theorem waveInner_magneticHamiltonian_eq_magneticForm (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hV : Continuous V) (hψ : IsTestFunction ψ) :
    waveInner ψ (magneticHamiltonian b coupling V ψ) =
      (magneticForm b coupling V ψ : ℂ) := by
  have hD (i : Fin 2) := hψ.covariantDerivative b coupling i
  have hDD (i : Fin 2) := (hD i).covariantDerivative b coupling i
  have hkin (i : Fin 2) := hψ.integrable_star_mul (hDD i).1.continuous
  have hpot : Integrable (fun x : Plane =>
      star (ψ x) * (((coupling ^ 2 * V x : ℝ) : ℂ) * ψ x)) :=
    hψ.integrable_star_mul
      ((Complex.continuous_ofReal.comp (continuous_const.mul hV)).mul hψ.1.continuous)
  have hrealpot : Integrable (fun x : Plane => coupling ^ 2 * V x * ‖ψ x‖ ^ 2) := by
    apply ((continuous_const.mul hV).mul (hψ.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    exact (hψ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mul_left
  have hpot_eq : (fun x : Plane => star (ψ x) * (((coupling ^ 2 * V x : ℝ) : ℂ) * ψ x)) =
      fun x => ((coupling ^ 2 * V x * ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [mul_left_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    simp only [Complex.ofReal_mul]
  have hinner : waveInner ψ (magneticHamiltonian b coupling V ψ) =
      (∑ i : Fin 2, waveInner ψ
        (covariantDerivative b coupling i (covariantDerivative b coupling i ψ))) +
      ∫ x, star (ψ x) * (((coupling ^ 2 * V x : ℝ) : ℂ) * ψ x) := by
    unfold waveInner magneticHamiltonian
    simp_rw [mul_add, Finset.mul_sum]
    rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hkin i)) hpot,
      integral_finsetSum Finset.univ (fun i _ => hkin i)]
  rw [hinner]
  simp_rw [waveInner_covariantDerivative b coupling _ hψ (hD _), waveInner_self_eq_mass]
  rw [hpot_eq, integral_complex_ofReal]
  simp only [magneticForm, mass]
  rw [integral_add (integrable_finsetSum Finset.univ
    (fun i _ => hψ.integrable_covariant_norm_sq b coupling i)) hrealpot,
    integral_finsetSum Finset.univ (fun i _ => hψ.integrable_covariant_norm_sq b coupling i)]
  simp

theorem re_waveInner_magneticHamiltonian_eq_magneticForm (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hV : Continuous V) (hψ : IsTestFunction ψ) :
    (waveInner ψ (magneticHamiltonian b coupling V ψ)).re = magneticForm b coupling V ψ := by
  rw [waveInner_magneticHamiltonian_eq_magneticForm b coupling hV hψ, Complex.ofReal_re]

end InfiniteZero
