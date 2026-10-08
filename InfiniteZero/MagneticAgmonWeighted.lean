import InfiniteZero.MagneticAgmonLocal

/-!
# Compactly localized exponential weights for magnetic eigenfunctions

The cutoff and its derivatives supply every compact support used below.
The weight and the eigenfunction need not have globally integrable energy.
No removal of cutoffs or global exponential-decay assertion is made here.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem continuous_cutoffGradientSq {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (cutoffGradientSq χ) := by
  apply continuous_finsetSum
  intro i _
  exact (contDiff_realPartialDerivative i hχ).continuous.pow 2

/-- A continuous multiplier is harmless on the compact support of the cutoff. -/
theorem integrable_mul_compact_sq_mul {χ f : Plane → ℝ} {φ : Wavefunction}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hf : Continuous f) (hφ : Continuous φ) :
    Integrable (fun x => f x * χ x ^ 2 * ‖φ x‖ ^ 2) := by
  apply ((hf.mul (hχ.pow 2)).mul (hφ.norm.pow 2)).integrable_of_hasCompactSupport
  exact ((hc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_left).mul_right

/-- The derivative of a compactly supported cutoff is still compactly supported. -/
theorem integrable_mul_cutoffGradientSq_mul {χ f : Plane → ℝ} {φ : Wavefunction}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hf : Continuous f) (hφ : Continuous φ) :
    Integrable (fun x => f x * cutoffGradientSq χ x * ‖φ x‖ ^ 2) := by
  simp_rw [cutoffGradientSq, Finset.mul_sum, Finset.sum_mul]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply ((hf.mul ((contDiff_realPartialDerivative i hχ).continuous.pow 2)).mul
    (hφ.norm.pow 2)).integrable_of_hasCompactSupport
  exact (((hc.fderiv_apply ℝ (coordinateVector i)).comp_left
    (g := fun t : ℝ => t ^ 2) (by simp)).mul_left).mul_right

/-- Dropping the nonnegative localized kinetic energy gives a variable-potential
version of the local forbidden-region estimate. -/
theorem cutoff_potential_le_gradient_error {b coupling E : ℝ} {V : Potential}
    {χ : Plane → ℝ} {φ : Wavefunction} (hV : Continuous V)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hφ : IsEigenfunction b coupling V E φ) :
    (∫ x : Plane, (coupling ^ 2 * V x - E) * χ x ^ 2 * ‖φ x‖ ^ 2) ≤
      ∫ x : Plane, cutoffGradientSq χ x * ‖φ x‖ ^ 2 := by
  let ψ : Wavefunction := fun x => (χ x : ℂ) * φ x
  have ht : IsTestFunction ψ := isTestFunction_compact_real_mul hχ hc hφ.1
  have hn := ht.integrable_norm_sq
  have hd := ht.integrable_magneticEnergyDensity b coupling hV
  have hp := integrable_mul_compact_sq_mul (f := fun x => coupling ^ 2 * V x - E)
    hχ.continuous hc
    ((continuous_const.mul hV).sub continuous_const) hφ.1.continuous
  have hnorm (x : Plane) : ‖ψ x‖ ^ 2 = χ x ^ 2 * ‖φ x‖ ^ 2 := by
    simp only [ψ, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ∫ x : Plane, magneticEnergyDensity b coupling V ψ x - E * ‖ψ x‖ ^ 2 := by
      apply integral_mono hp (hd.sub (hn.const_mul E))
      intro x
      have hk : 0 ≤ ∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      change (coupling ^ 2 * V x - E) * χ x ^ 2 * ‖φ x‖ ^ 2 ≤
        magneticEnergyDensity b coupling V ψ x - E * ‖ψ x‖ ^ 2
      simp only [magneticEnergyDensity, hnorm]
      nlinarith only [hk]
    _ = magneticForm b coupling V ψ - E * mass ψ := by
      rw [integral_sub hd (hn.const_mul E), integral_const_mul]
      rfl
    _ = _ := magneticForm_cutoff_eigenfunction hV hχ hc hφ

/-- The integrated weighted local estimate. All terms are integrable because
`η` and its derivatives have compact support; `F` needs no global bound. -/
theorem magnetic_agmon_weighted {b coupling E : ℝ} {V : Potential}
    {η F : Plane → ℝ} {φ : Wavefunction} (hV : Continuous V)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hF : ContDiff ℝ ∞ F) (hφ : IsEigenfunction b coupling V E φ) :
    (∫ x : Plane, (coupling ^ 2 * V x - E - 2 * cutoffGradientSq F x) *
      (η x * Real.exp (F x)) ^ 2 * ‖φ x‖ ^ 2) ≤
      2 * ∫ x : Plane, Real.exp (F x) ^ 2 * cutoffGradientSq η x * ‖φ x‖ ^ 2 := by
  let χ : Plane → ℝ := fun x => η x * Real.exp (F x)
  have hχ : ContDiff ℝ ∞ χ := hη.mul hF.exp
  have hχc : HasCompactSupport χ := hc.mul_right
  have hp := integrable_mul_compact_sq_mul (f := fun x => coupling ^ 2 * V x - E)
    hχ.continuous hχc
    ((continuous_const.mul hV).sub continuous_const) hφ.1.continuous
  have hg := integrable_mul_compact_sq_mul hχ.continuous hχc
    (continuous_cutoffGradientSq hF) hφ.1.continuous
  have he := integrable_mul_cutoffGradientSq_mul hη hc
    (hF.exp.continuous.pow 2) hφ.1.continuous
  have hgrad := integrable_cutoffGradientSq_mul hχ hχc hφ.1.continuous
  have hbound : (∫ x : Plane, cutoffGradientSq χ x * ‖φ x‖ ^ 2) ≤
      2 * (∫ x : Plane, Real.exp (F x) ^ 2 * cutoffGradientSq η x * ‖φ x‖ ^ 2) +
        2 * (∫ x : Plane, cutoffGradientSq F x * χ x ^ 2 * ‖φ x‖ ^ 2) := by
    calc
      _ ≤ ∫ x : Plane,
          2 * (Real.exp (F x) ^ 2 * cutoffGradientSq η x * ‖φ x‖ ^ 2) +
          2 * (cutoffGradientSq F x * χ x ^ 2 * ‖φ x‖ ^ 2) := by
        apply integral_mono hgrad ((he.const_mul 2).add (hg.const_mul 2))
        intro x
        have hb := mul_le_mul_of_nonneg_right
          (cutoffGradientSq_mul_exp_le ((hη.differentiable (by simp)) x)
            ((hF.differentiable (by simp)) x)) (sq_nonneg ‖φ x‖)
        dsimp only [χ, Pi.add_apply]
        nlinarith only [hb]
      _ = _ := by
        rw [integral_add (he.const_mul 2) (hg.const_mul 2), integral_const_mul,
          integral_const_mul]
  have hpot := cutoff_potential_le_gradient_error hV hχ hχc hφ
  have heq : (∫ x : Plane, (coupling ^ 2 * V x - E - 2 * cutoffGradientSq F x) *
      χ x ^ 2 * ‖φ x‖ ^ 2) =
      (∫ x : Plane, (coupling ^ 2 * V x - E) * χ x ^ 2 * ‖φ x‖ ^ 2) -
        2 * (∫ x : Plane, cutoffGradientSq F x * χ x ^ 2 * ‖φ x‖ ^ 2) := by
    calc
      _ = ∫ x : Plane, (coupling ^ 2 * V x - E) * χ x ^ 2 * ‖φ x‖ ^ 2 -
          2 * (cutoffGradientSq F x * χ x ^ 2 * ‖φ x‖ ^ 2) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_sub hp (hg.const_mul 2), integral_const_mul]
  change (∫ x : Plane, (coupling ^ 2 * V x - E - 2 * cutoffGradientSq F x) *
    χ x ^ 2 * ‖φ x‖ ^ 2) ≤ _
  rw [heq]
  linarith only [hpot, hbound]

/-- Coercivity for a compactly localized exponential weight, for any real
potential and any lower bound on its effective weighted reserve. -/
theorem weighted_cutoff_mass_le_gradient_error {b coupling E δ : ℝ} {V : Potential}
    {η F : Plane → ℝ} {φ : Wavefunction} (hV : Continuous V)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hF : ContDiff ℝ ∞ F)
    (hφ : IsEigenfunction b coupling V E φ)
    (hreserve : ∀ x, η x ≠ 0 → δ ≤ coupling ^ 2 * V x - E - 2 * cutoffGradientSq F x) :
    δ * mass (fun x => ((η x * Real.exp (F x) : ℝ) : ℂ) * φ x) ≤
      2 * ∫ x : Plane, Real.exp (F x) ^ 2 * cutoffGradientSq η x * ‖φ x‖ ^ 2 := by
  let χ : Plane → ℝ := fun x => η x * Real.exp (F x)
  have hχ : ContDiff ℝ ∞ χ := hη.mul hF.exp
  have hχc : HasCompactSupport χ := hc.mul_right
  have ht := isTestFunction_compact_real_mul hχ hχc hφ.1
  have hcoeff : Continuous (fun x => coupling ^ 2 * V x - E -
      2 * cutoffGradientSq F x) :=
    ((continuous_const.mul hV).sub continuous_const).sub
      (continuous_const.mul (continuous_cutoffGradientSq hF))
  have hi := integrable_mul_compact_sq_mul hχ.continuous hχc hcoeff hφ.1.continuous
  have hnorm (x : Plane) : ‖(χ x : ℂ) * φ x‖ ^ 2 = χ x ^ 2 * ‖φ x‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ = ∫ x : Plane, (δ) * ‖(χ x : ℂ) * φ x‖ ^ 2 :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ x : Plane, (coupling ^ 2 * V x - E - 2 * cutoffGradientSq F x) *
        χ x ^ 2 * ‖φ x‖ ^ 2 := by
      apply integral_mono (ht.integrable_norm_sq.const_mul (δ)) hi
      intro x
      change (δ) * ‖(χ x : ℂ) * φ x‖ ^ 2 ≤
        (coupling ^ 2 * V x - E - 2 * cutoffGradientSq F x) * χ x ^ 2 * ‖φ x‖ ^ 2
      rw [hnorm]
      by_cases hx : η x = 0
      · simp [χ, hx]
      · have hr' := hreserve x hx
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hr'
          (mul_nonneg (sq_nonneg (χ x)) (sq_nonneg ‖φ x‖))
    _ ≤ _ := magnetic_agmon_weighted hV hη hc hF hφ

end InfiniteZero
