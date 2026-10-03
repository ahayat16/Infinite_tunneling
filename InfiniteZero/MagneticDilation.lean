import InfiniteZero.AffineScaleL2

/-!
# Global unitary dilation of the magnetic test form

In two dimensions the inverse square-root spatial dilation carries the
same inverse square-root amplitude. It preserves mass, parity and smooth
compact support. The magnetic field parameter becomes one, and the
unscaled form acquires exactly one inverse coupling factor.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

private def planarUnitaryDilation (r : ℝ) (ψ : Wavefunction) : Wavefunction :=
  fun y => (r⁻¹ : ℂ) * ψ (r⁻¹ • y)

/-- The global unitary change of variables `x = coupling⁻¹ᐟ² y`. -/
def magneticDilation (coupling : ℝ) (ψ : Wavefunction) : Wavefunction :=
  planarUnitaryDilation (Real.sqrt coupling) ψ

theorem magneticDilation_apply (coupling : ℝ) (ψ : Wavefunction) (y : Plane) :
    magneticDilation coupling ψ y =
      ((Real.sqrt coupling)⁻¹ : ℂ) * ψ ((Real.sqrt coupling)⁻¹ • y) := rfl

private theorem mass_planarUnitaryDilation {r : ℝ} (hr : 0 < r) (ψ : Wavefunction) :
    mass (planarUnitaryDilation r ψ) = mass ψ := by
  simp only [mass, planarUnitaryDilation, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Plane => ‖ψ x‖ ^ 2) hr.le]
  simp only [Plane, finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

theorem mass_magneticDilation {coupling : ℝ} (hc : 0 < coupling) (ψ : Wavefunction) :
    mass (magneticDilation coupling ψ) = mass ψ :=
  mass_planarUnitaryDilation (Real.sqrt_pos.mpr hc) ψ

theorem contDiff_magneticDilation (coupling : ℝ) {ψ : Wavefunction}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (magneticDilation coupling ψ) :=
  contDiff_const.mul (hψ.comp (contDiff_id.const_smul _))

theorem IsTestFunction.magneticDilation {coupling : ℝ} (hc : 0 < coupling)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    IsTestFunction (magneticDilation coupling ψ) := by
  refine ⟨contDiff_magneticDilation coupling hψ.1, ?_⟩
  have hr : (Real.sqrt coupling)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hc).ne'
  have hs : HasCompactSupport (fun y : Plane => ψ ((Real.sqrt coupling)⁻¹ • y)) := by
    simpa only [Homeomorph.smul_apply, Units.val_mk0] using
      hψ.2.comp_homeomorph (Homeomorph.smul (Units.mk0 ((Real.sqrt coupling)⁻¹) hr))
  exact hs.mul_left

theorem IsNormalizedTest.magneticDilation {coupling : ℝ} (hc : 0 < coupling)
    {ψ : Wavefunction} (hψ : IsNormalizedTest ψ) :
    IsNormalizedTest (magneticDilation coupling ψ) :=
  ⟨hψ.1.magneticDilation hc, (mass_magneticDilation hc ψ).trans hψ.2⟩

theorem HasParity.magneticDilation {even : Bool} {ψ : Wavefunction}
    (hψ : HasParity even ψ) (coupling : ℝ) :
    HasParity even (magneticDilation coupling ψ) := by
  intro y
  simp only [magneticDilation_apply, smul_neg]
  rw [hψ ((Real.sqrt coupling)⁻¹ • y)]
  cases even <;> simp

theorem magneticDilation_inv_cancel {coupling : ℝ} (hc : 0 < coupling) (ψ : Wavefunction) :
    magneticDilation coupling⁻¹ (magneticDilation coupling ψ) = ψ := by
  funext y
  have hr := (Real.sqrt_pos.mpr hc).ne'
  simp only [magneticDilation_apply, Real.sqrt_inv, inv_inv, smul_smul]
  rw [inv_mul_cancel₀ hr, one_smul, ← mul_assoc]
  simp [hr]

theorem magneticDilation_cancel_inv {coupling : ℝ} (hc : 0 < coupling) (ψ : Wavefunction) :
    magneticDilation coupling (magneticDilation coupling⁻¹ ψ) = ψ := by
  simpa only [inv_inv] using magneticDilation_inv_cancel (inv_pos.mpr hc) ψ

theorem magneticDilation_bijective {coupling : ℝ} (hc : 0 < coupling) :
    Function.Bijective (magneticDilation coupling) :=
  ⟨Function.LeftInverse.injective (magneticDilation_inv_cancel hc),
    Function.RightInverse.surjective (magneticDilation_cancel_inv hc)⟩

private theorem partialDerivative_planarUnitaryDilation {r : ℝ} {ψ : Wavefunction}
    (hψ : Differentiable ℝ ψ) (i : Fin 2) (y : Plane) :
    partialDerivative i (planarUnitaryDilation r ψ) y =
      ((r⁻¹) ^ 2 : ℂ) * partialDerivative i ψ (r⁻¹ • y) := by
  have hd : Differentiable ℝ (ψ ∘ affineScale 0 r⁻¹) :=
    hψ.comp ((contDiff_affineScale 0 r⁻¹).differentiable (by simp))
  have heq : planarUnitaryDilation r ψ = (r⁻¹ : ℂ) • (ψ ∘ affineScale 0 r⁻¹) := by
    ext x
    simp [planarUnitaryDilation, affineScale]
  rw [heq, partialDerivative, fderiv_const_smul (hd y)]
  change (r⁻¹ : ℂ) * partialDerivative i (ψ ∘ affineScale 0 r⁻¹) y = _
  rw [partialDerivative_affineScale hψ]
  simp only [affineScale, zero_add]
  push_cast
  ring

private theorem covariantDerivative_planarUnitaryDilation {r : ℝ} (hr : r ≠ 0)
    (b : ℝ) {ψ : Wavefunction} (hψ : Differentiable ℝ ψ) (i : Fin 2) (y : Plane) :
    covariantDerivative b 1 i (planarUnitaryDilation r ψ) y =
      ((r⁻¹) ^ 2 : ℂ) * covariantDerivative b (r ^ 2) i ψ (r⁻¹ • y) := by
  have hp : perpCoordinate (r⁻¹ • y) i = r⁻¹ * perpCoordinate y i := by
    simp only [perpCoordinate, PiLp.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  simp only [covariantDerivative, partialDerivative_planarUnitaryDilation hψ,
    planarUnitaryDilation, hp]
  push_cast
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  field_simp

private theorem magneticForm_planarUnitaryDilation {r : ℝ} (hr : 0 < r)
    (b : ℝ) (V : Potential) {ψ : Wavefunction} (hψ : Differentiable ℝ ψ) :
    magneticForm b 1 (fun y => r ^ 2 * V (r⁻¹ • y)) (planarUnitaryDilation r ψ) =
      (r ^ 2)⁻¹ * magneticForm b (r ^ 2) V ψ := by
  let F : Plane → ℝ := fun x =>
    (∑ i : Fin 2, ‖covariantDerivative b (r ^ 2) i ψ x‖ ^ 2) +
      (r ^ 2) ^ 2 * V x * ‖ψ x‖ ^ 2
  have hpoint (y : Plane) :
      (∑ i : Fin 2, ‖covariantDerivative b 1 i (planarUnitaryDilation r ψ) y‖ ^ 2) +
        1 ^ 2 * (r ^ 2 * V (r⁻¹ • y)) * ‖planarUnitaryDilation r ψ y‖ ^ 2 =
      (r ^ 4)⁻¹ * F (r⁻¹ • y) := by
    simp only [covariantDerivative_planarUnitaryDilation hr.ne' b hψ,
      planarUnitaryDilation, norm_mul, norm_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, mul_pow,
      F, Fin.sum_univ_two, one_pow, one_mul]
    field_simp
  unfold magneticForm
  simp_rw [hpoint]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume F hr.le]
  simp only [Plane, finrank_euclideanSpace_fin, smul_eq_mul]
  change (r ^ 4)⁻¹ * (r ^ 2 * ∫ x, F x) = (r ^ 2)⁻¹ * ∫ x, F x
  field_simp

/-- Exact global rescaling of the test form, with its potential and energy factors. -/
theorem magneticForm_magneticDilation (b : ℝ) (V : Potential) {coupling : ℝ}
    (hc : 0 < coupling) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    magneticForm b 1
        (fun y => coupling * V ((Real.sqrt coupling)⁻¹ • y))
        (magneticDilation coupling ψ) =
      coupling⁻¹ * magneticForm b coupling V ψ := by
  simpa only [Real.sq_sqrt hc.le, magneticDilation] using
    magneticForm_planarUnitaryDilation (Real.sqrt_pos.mpr hc) b V
      (hψ.1.differentiable (by simp))

end InfiniteZero
