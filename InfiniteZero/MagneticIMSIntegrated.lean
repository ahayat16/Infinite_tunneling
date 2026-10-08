import InfiniteZero.MagneticIMS
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Integration of the concrete pointwise IMS identity on smooth compactly
supported test functions. No assertion about the closed form domain is made.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem hasCompactSupport_partialDerivative (i : Fin 2) {ψ : Wavefunction}
    (hψ : HasCompactSupport ψ) : HasCompactSupport (partialDerivative i ψ) :=
  hψ.fderiv_apply ℝ (coordinateVector i)

theorem hasCompactSupport_covariantDerivative (b coupling : ℝ) (i : Fin 2)
    {ψ : Wavefunction} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (covariantDerivative b coupling i ψ) := by
  have hd : HasCompactSupport (fun x => -Complex.I * partialDerivative i ψ x) :=
    (hasCompactSupport_partialDerivative i hψ).mul_left
  have ha : HasCompactSupport (fun x =>
      ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ) * ψ x) := hψ.mul_left
  exact hd.sub ha

theorem IsTestFunction.real_mul {χ : Plane → ℝ} {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) (hχ : ContDiff ℝ ∞ χ) :
    IsTestFunction (fun x => (χ x : ℂ) * ψ x) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp hχ).mul hψ.1, hψ.2.mul_left⟩

theorem IsTestFunction.integrable_norm_sq {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) : Integrable (fun x => ‖ψ x‖ ^ 2) := by
  apply (hψ.1.continuous.norm.pow 2).integrable_of_hasCompactSupport
  exact hψ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)

theorem IsTestFunction.integrable_covariant_norm_sq (b coupling : ℝ) (i : Fin 2)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    Integrable (fun x => ‖covariantDerivative b coupling i ψ x‖ ^ 2) := by
  apply ((contDiff_covariantDerivative b coupling i hψ.1).continuous.norm.pow 2).integrable_of_hasCompactSupport
  exact (hasCompactSupport_covariantDerivative b coupling i hψ.2).comp_left
    (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)

/-- Continuity of the potential suffices; only its values on a compact set occur. -/
theorem IsTestFunction.integrable_magneticEnergyDensity (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hψ : IsTestFunction ψ) (hV : Continuous V) :
    Integrable (magneticEnergyDensity b coupling V ψ) := by
  have hkin := integrable_finsetSum Finset.univ
    (fun (i : Fin 2) _ => hψ.integrable_covariant_norm_sq b coupling i)
  have hpot : Integrable (fun x => coupling ^ 2 * V x * ‖ψ x‖ ^ 2) := by
    apply ((continuous_const.mul hV).mul (hψ.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    exact (hψ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mul_left
  exact hkin.add hpot

theorem contDiff_realPartialDerivative (i : Fin 2) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (realPartialDerivative i χ) :=
  (hχ.fderiv_right (by simp)).clm_apply contDiff_const

theorem continuous_magneticIMSError {χ₀ χ₁ : Plane → ℝ}
    (hχ₀ : ContDiff ℝ ∞ χ₀) (hχ₁ : ContDiff ℝ ∞ χ₁) :
    Continuous (magneticIMSError χ₀ χ₁) := by
  apply continuous_finsetSum
  intro i _
  exact ((contDiff_realPartialDerivative i hχ₀).continuous.pow 2).add
    ((contDiff_realPartialDerivative i hχ₁).continuous.pow 2)

/-- The cutoffs need not have compact support or globally bounded derivatives. -/
theorem IsTestFunction.integrable_magneticIMSError {χ₀ χ₁ : Plane → ℝ}
    {ψ : Wavefunction} (hψ : IsTestFunction ψ)
    (hχ₀ : ContDiff ℝ ∞ χ₀) (hχ₁ : ContDiff ℝ ∞ χ₁) :
    Integrable (fun x => magneticIMSError χ₀ χ₁ x * ‖ψ x‖ ^ 2) := by
  apply ((continuous_magneticIMSError hχ₀ hχ₁).mul (hψ.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  exact (hψ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mul_left

/-- Integrated IMS on the original test-function form, with integrability proved. -/
theorem magneticForm_ims (b coupling : ℝ) {V : Potential}
    {χ₀ χ₁ : Plane → ℝ} {ψ : Wavefunction} (hV : Continuous V)
    (hψ : IsTestFunction ψ) (hχ₀ : ContDiff ℝ ∞ χ₀) (hχ₁ : ContDiff ℝ ∞ χ₁)
    (hpartition : ∀ x, χ₀ x ^ 2 + χ₁ x ^ 2 = 1) :
    magneticForm b coupling V (fun x => (χ₀ x : ℂ) * ψ x) +
      magneticForm b coupling V (fun x => (χ₁ x : ℂ) * ψ x) =
      magneticForm b coupling V ψ +
        ∫ x : Plane, magneticIMSError χ₀ χ₁ x * ‖ψ x‖ ^ 2 := by
  have h₀ := (hψ.real_mul hχ₀).integrable_magneticEnergyDensity b coupling hV
  have h₁ := (hψ.real_mul hχ₁).integrable_magneticEnergyDensity b coupling hV
  have hfull := hψ.integrable_magneticEnergyDensity b coupling hV
  have herr := hψ.integrable_magneticIMSError hχ₀ hχ₁
  simp only [magneticForm_eq_integral_density]
  rw [← integral_add h₀ h₁, ← integral_add hfull herr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => magneticEnergyDensity_ims b coupling V
    ((hχ₀.differentiable (by simp)) x) ((hχ₁.differentiable (by simp)) x)
    ((hψ.1.differentiable (by simp)) x) hpartition

/-- The mass partition uses the same actual Lebesgue integrals. -/
theorem mass_ims {χ₀ χ₁ : Plane → ℝ} {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) (hχ₀ : ContDiff ℝ ∞ χ₀) (hχ₁ : ContDiff ℝ ∞ χ₁)
    (hpartition : ∀ x, χ₀ x ^ 2 + χ₁ x ^ 2 = 1) :
    mass (fun x => (χ₀ x : ℂ) * ψ x) +
      mass (fun x => (χ₁ x : ℂ) * ψ x) = mass ψ := by
  unfold mass
  rw [← integral_add (hψ.real_mul hχ₀).integrable_norm_sq
    (hψ.real_mul hχ₁).integrable_norm_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    realCutoff_mass_partition (χ₀ x) (χ₁ x) (ψ x) (hpartition x)

/-- IMS with a spectral shift, in the direction used for lower form bounds. -/
theorem magneticForm_sub_mass_ims (b coupling E : ℝ) {V : Potential}
    {χ₀ χ₁ : Plane → ℝ} {ψ : Wavefunction} (hV : Continuous V)
    (hψ : IsTestFunction ψ) (hχ₀ : ContDiff ℝ ∞ χ₀) (hχ₁ : ContDiff ℝ ∞ χ₁)
    (hpartition : ∀ x, χ₀ x ^ 2 + χ₁ x ^ 2 = 1) :
    magneticForm b coupling V ψ - E * mass ψ =
      (magneticForm b coupling V (fun x => (χ₀ x : ℂ) * ψ x) -
        E * mass (fun x => (χ₀ x : ℂ) * ψ x)) +
      (magneticForm b coupling V (fun x => (χ₁ x : ℂ) * ψ x) -
        E * mass (fun x => (χ₁ x : ℂ) * ψ x)) -
      ∫ x : Plane, magneticIMSError χ₀ χ₁ x * ‖ψ x‖ ^ 2 := by
  have hform := magneticForm_ims b coupling hV hψ hχ₀ hχ₁ hpartition
  have hmass := mass_ims hψ hχ₀ hχ₁ hpartition
  linear_combination -hform + E * hmass

end InfiniteZero
