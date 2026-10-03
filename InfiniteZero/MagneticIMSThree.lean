import InfiniteZero.MagneticIMSIntegrated

/-!
# Three-piece IMS from two successive localizations

Two smooth real partitions are applied successively. The compatibility
`ηL * χR = χR` identifies the second localized piece with the right cutoff.
All integrability follows from the original compactly supported test state.
No statement about the closed form domain is used.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

private theorem ims_three_right_eq {ηL χR : Plane → ℝ} (ψ : Wavefunction)
    (hcompat : ∀ x, ηL x * χR x = χR x) :
    (fun x => (χR x : ℂ) * ((ηL x : ℂ) * ψ x)) =
      (fun x => (χR x : ℂ) * ψ x) := by
  funext x
  calc
    _ = ((ηL x * χR x : ℝ) : ℂ) * ψ x := by push_cast; ring
    _ = _ := by rw [hcompat x]

private theorem ims_three_outer_eq (ηL ηR : Plane → ℝ) (ψ : Wavefunction) :
    (fun x => (ηR x : ℂ) * ((ηL x : ℂ) * ψ x)) =
      (fun x => ((ηR x * ηL x : ℝ) : ℂ) * ψ x) := by
  simp only [Complex.ofReal_mul, mul_assoc]

/-- The exact three-piece mass identity uses the same localization as IMS. -/
theorem mass_ims_three {χL ηL χR ηR : Plane → ℝ} {ψ : Wavefunction}
    (hψ : IsTestFunction ψ)
    (hχL : ContDiff ℝ ∞ χL) (hηL : ContDiff ℝ ∞ ηL)
    (hχR : ContDiff ℝ ∞ χR) (hηR : ContDiff ℝ ∞ ηR)
    (hpartitionL : ∀ x, χL x ^ 2 + ηL x ^ 2 = 1)
    (hpartitionR : ∀ x, χR x ^ 2 + ηR x ^ 2 = 1)
    (hcompat : ∀ x, ηL x * χR x = χR x) :
    mass (fun x => (χL x : ℂ) * ψ x) +
      mass (fun x => (χR x : ℂ) * ψ x) +
      mass (fun x => ((ηR x * ηL x : ℝ) : ℂ) * ψ x) = mass ψ := by
  have hL := mass_ims hψ hχL hηL hpartitionL
  have hR := mass_ims (hψ.real_mul hηL) hχR hηR hpartitionR
  rw [ims_three_right_eq ψ hcompat, ims_three_outer_eq ηL ηR ψ] at hR
  linarith only [hL, hR]

/-- The two losses are kept separate: the second acts on the state already
localized by `ηL`. -/
theorem magneticForm_sub_mass_ims_three (b coupling E : ℝ) {V : Potential}
    {χL ηL χR ηR : Plane → ℝ} {ψ : Wavefunction} (hV : Continuous V)
    (hψ : IsTestFunction ψ)
    (hχL : ContDiff ℝ ∞ χL) (hηL : ContDiff ℝ ∞ ηL)
    (hχR : ContDiff ℝ ∞ χR) (hηR : ContDiff ℝ ∞ ηR)
    (hpartitionL : ∀ x, χL x ^ 2 + ηL x ^ 2 = 1)
    (hpartitionR : ∀ x, χR x ^ 2 + ηR x ^ 2 = 1)
    (hcompat : ∀ x, ηL x * χR x = χR x) :
    magneticForm b coupling V ψ - E * mass ψ =
      (magneticForm b coupling V (fun x => (χL x : ℂ) * ψ x) -
        E * mass (fun x => (χL x : ℂ) * ψ x)) +
      (magneticForm b coupling V (fun x => (χR x : ℂ) * ψ x) -
        E * mass (fun x => (χR x : ℂ) * ψ x)) +
      (magneticForm b coupling V (fun x => ((ηR x * ηL x : ℝ) : ℂ) * ψ x) -
        E * mass (fun x => ((ηR x * ηL x : ℝ) : ℂ) * ψ x)) -
      (∫ x : Plane, magneticIMSError χL ηL x * ‖ψ x‖ ^ 2) -
      (∫ x : Plane, magneticIMSError χR ηR x * ‖(ηL x : ℂ) * ψ x‖ ^ 2) := by
  have hL := magneticForm_sub_mass_ims b coupling E hV hψ hχL hηL hpartitionL
  have hR := magneticForm_sub_mass_ims b coupling E hV
    (hψ.real_mul hηL) hχR hηR hpartitionR
  rw [ims_three_right_eq ψ hcompat, ims_three_outer_eq ηL ηR ψ] at hR
  linarith only [hL, hR]

/-- A pointwise bound on the IMS coefficient gives an integral bound;
the integrability of both sides follows from the test-function hypotheses. -/
theorem integral_magneticIMSError_le {χ₀ χ₁ : Plane → ℝ} {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) (hχ₀ : ContDiff ℝ ∞ χ₀) (hχ₁ : ContDiff ℝ ∞ χ₁)
    {C : ℝ} (hC : ∀ x, magneticIMSError χ₀ χ₁ x ≤ C) :
    (∫ x : Plane, magneticIMSError χ₀ χ₁ x * ‖ψ x‖ ^ 2) ≤ C * mass ψ := by
  have h := integral_mono (hψ.integrable_magneticIMSError hχ₀ hχ₁)
    (hψ.integrable_norm_sq.const_mul C)
    (fun x => mul_le_mul_of_nonneg_right (hC x) (sq_nonneg ‖ψ x‖))
  simpa only [integral_const_mul, mass] using h

theorem IsTestFunction.mass_real_mul_le {η : Plane → ℝ} {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) (hη : ContDiff ℝ ∞ η) (hbound : ∀ x, |η x| ≤ 1) :
    mass (fun x => (η x : ℂ) * ψ x) ≤ mass ψ := by
  apply integral_mono (hψ.real_mul hη).integrable_norm_sq hψ.integrable_norm_sq
  intro x
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)).trans_eq (one_mul _)

/-- The sum of the three shifted energies, minus a fixed mass loss, is
bounded by the original shifted energy. -/
theorem magneticForm_sub_mass_ims_three_lower (b coupling E : ℝ) {V : Potential}
    {χL ηL χR ηR : Plane → ℝ} {ψ : Wavefunction} (hV : Continuous V)
    (hψ : IsTestFunction ψ)
    (hχL : ContDiff ℝ ∞ χL) (hηL : ContDiff ℝ ∞ ηL)
    (hχR : ContDiff ℝ ∞ χR) (hηR : ContDiff ℝ ∞ ηR)
    (hpartitionL : ∀ x, χL x ^ 2 + ηL x ^ 2 = 1)
    (hpartitionR : ∀ x, χR x ^ 2 + ηR x ^ 2 = 1)
    (hcompat : ∀ x, ηL x * χR x = χR x)
    {CL CR : ℝ} (_hCL : 0 ≤ CL) (hCR : 0 ≤ CR)
    (herrorL : ∀ x, magneticIMSError χL ηL x ≤ CL)
    (herrorR : ∀ x, magneticIMSError χR ηR x ≤ CR)
    (hηLbound : ∀ x, |ηL x| ≤ 1) :
    (magneticForm b coupling V (fun x => (χL x : ℂ) * ψ x) -
      E * mass (fun x => (χL x : ℂ) * ψ x)) +
    (magneticForm b coupling V (fun x => (χR x : ℂ) * ψ x) -
      E * mass (fun x => (χR x : ℂ) * ψ x)) +
    (magneticForm b coupling V (fun x => ((ηR x * ηL x : ℝ) : ℂ) * ψ x) -
      E * mass (fun x => ((ηR x * ηL x : ℝ) : ℂ) * ψ x)) -
    (CL + CR) * mass ψ ≤ magneticForm b coupling V ψ - E * mass ψ := by
  have hid := magneticForm_sub_mass_ims_three b coupling E hV hψ
    hχL hηL hχR hηR hpartitionL hpartitionR hcompat
  have hL := integral_magneticIMSError_le hψ hχL hηL herrorL
  have hR := (integral_magneticIMSError_le (hψ.real_mul hηL) hχR hηR herrorR).trans
    (mul_le_mul_of_nonneg_left (hψ.mass_real_mul_le hηL hηLbound) hCR)
  nlinarith only [hid, hL, hR]

end InfiniteZero
