import InfiniteZero.MagneticDilationPotential
import InfiniteZero.MagneticIMSIntegrated

/-!
# Comparing magnetic test forms by their potentials

At fixed field and coupling, the kinetic terms cancel exactly. A uniform
pointwise potential difference therefore controls the form difference by
its size times the test mass. Applying this to the globally dilated
potentials gives one Lipschitz constant for all normalized tests.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- The exact form difference contains only the potential difference. -/
theorem magneticForm_sub_eq_potential_integral (b coupling : ℝ) {V W : Potential}
    (hV : Continuous V) (hW : Continuous W) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    magneticForm b coupling V ψ - magneticForm b coupling W ψ =
      coupling ^ 2 * ∫ x : Plane, (V x - W x) * ‖ψ x‖ ^ 2 := by
  calc
    _ = ∫ x : Plane, magneticEnergyDensity b coupling V ψ x -
        magneticEnergyDensity b coupling W ψ x :=
      (integral_sub (hψ.integrable_magneticEnergyDensity b coupling hV)
        (hψ.integrable_magneticEnergyDensity b coupling hW)).symm
    _ = ∫ x : Plane, coupling ^ 2 * ((V x - W x) * ‖ψ x‖ ^ 2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [magneticEnergyDensity]
        ring
    _ = _ := integral_const_mul _ _

/-- A uniform potential bound controls the form difference on every actual test. -/
theorem abs_magneticForm_sub_le (b coupling : ℝ) {V W : Potential}
    (hV : Continuous V) (hW : Continuous W) {ψ : Wavefunction} (hψ : IsTestFunction ψ)
    {δ : ℝ} (hbound : ∀ x, |V x - W x| ≤ δ) :
    |magneticForm b coupling V ψ - magneticForm b coupling W ψ| ≤
      coupling ^ 2 * δ * mass ψ := by
  rw [magneticForm_sub_eq_potential_integral b coupling hV hW hψ,
    abs_mul, abs_of_nonneg (sq_nonneg coupling)]
  have hi : |∫ x : Plane, (V x - W x) * ‖ψ x‖ ^ 2| ≤ δ * mass ψ := by
    calc
      _ ≤ ∫ x : Plane, δ * ‖ψ x‖ ^ 2 := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le (hψ.integrable_norm_sq.const_mul δ)
        exact Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖ψ x‖)]
          exact mul_le_mul_of_nonneg_right (hbound x) (sq_nonneg _)
      _ = _ := integral_const_mul _ _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (sq_nonneg coupling)

/-- Spatial continuity of the potential after any fixed dilation. -/
theorem continuous_magneticDilationPotential {V : Potential} (hV : Continuous V)
    (coupling : ℝ) : Continuous (magneticDilationPotential V coupling) :=
  continuous_const.mul (hV.comp (continuous_id.const_smul _))

/-- The bound is fixed before the field, two positive couplings, and the test. -/
theorem exists_magneticForm_dilationPotential_mass_bound {V : Potential}
    (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V) :
    ∃ C > 0, ∀ (b c μ : ℝ), 0 < c → 0 < μ →
      ∀ ψ : Wavefunction, IsTestFunction ψ →
      |magneticForm b 1 (magneticDilationPotential V c) ψ -
        magneticForm b 1 (magneticDilationPotential V μ) ψ| ≤
        C * |c - μ| * mass ψ := by
  obtain ⟨C, hC, hbound⟩ := exists_magneticDilationPotential_lipschitz hV hcompact
  refine ⟨C, hC, fun b c μ hc hμ ψ hψ => ?_⟩
  simpa only [one_pow, one_mul] using abs_magneticForm_sub_le b 1
    (continuous_magneticDilationPotential hV.continuous c)
    (continuous_magneticDilationPotential hV.continuous μ) hψ (hbound c μ hc hμ)

/-- A single coupling Lipschitz constant works for all normalized tests at fixed field. -/
theorem exists_magneticForm_dilationPotential_lipschitz {V : Potential}
    (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V) :
    ∃ C > 0, ∀ (b c μ : ℝ), 0 < c → 0 < μ →
      ∀ ψ : Wavefunction, IsNormalizedTest ψ →
      |magneticForm b 1 (magneticDilationPotential V c) ψ -
        magneticForm b 1 (magneticDilationPotential V μ) ψ| ≤ C * |c - μ| := by
  obtain ⟨C, hC, hbound⟩ := exists_magneticForm_dilationPotential_mass_bound hV hcompact
  refine ⟨C, hC, fun b c μ hc hμ ψ hψ => ?_⟩
  simpa only [hψ.2, mul_one] using hbound b c μ hc hμ ψ hψ.1

end InfiniteZero
