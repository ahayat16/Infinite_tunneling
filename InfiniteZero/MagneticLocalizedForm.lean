import InfiniteZero.AtomicLocalizationEnergy

/-!
# Localized forms only depend on the potential where the cutoff is nonzero

These identities isolate a single well in a double-well localization.
Outside both supports the magnetic form is nonnegative; its shifted
energy therefore retains the full negative-energy reserve.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem magneticForm_real_cutoff_eq_of_potential_mul_eq
    (b coupling : ℝ) {V W : Potential} {χ : Plane → ℝ}
    (hVW : ∀ x, V x * χ x = W x * χ x) (ψ : Wavefunction) :
    magneticForm b coupling V (fun x => (χ x : ℂ) * ψ x) =
      magneticForm b coupling W (fun x => (χ x : ℂ) * ψ x) := by
  simp only [magneticForm_eq_integral_density]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [magneticEnergyDensity, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    congr 1
    linear_combination coupling ^ 2 * χ x * ‖ψ x‖ ^ 2 * hVW x

theorem magneticForm_zero_potential_nonneg (b coupling : ℝ) (ψ : Wavefunction) :
    0 ≤ magneticForm b coupling 0 ψ := by
  rw [magneticForm_eq_integral_density]
  apply integral_nonneg
  intro x
  simpa only [magneticEnergyDensity, Pi.zero_apply, mul_zero, zero_mul, add_zero] using
    magneticKinetic_nonneg b coupling ψ x

theorem magneticForm_real_cutoff_nonneg_of_potential_mul_zero
    (b coupling : ℝ) {V : Potential} {χ : Plane → ℝ}
    (hV : ∀ x, V x * χ x = 0) (ψ : Wavefunction) :
    0 ≤ magneticForm b coupling V (fun x => (χ x : ℂ) * ψ x) := by
  rw [magneticForm_real_cutoff_eq_of_potential_mul_eq b coupling
    (W := 0) (fun x => by simpa using hV x)]
  exact magneticForm_zero_potential_nonneg b coupling _

end InfiniteZero
