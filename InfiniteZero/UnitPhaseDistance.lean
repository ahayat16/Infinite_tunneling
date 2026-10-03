import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Phase alignment of two unit vectors

A scalar phase aligns two unit vectors with squared distance controlled
by twice their overlap deficit. No continuous choice of phases is assumed.
-/

noncomputable section
namespace InfiniteZero

/-- Unit vectors admit a phase alignment controlled only by their overlap. -/
theorem exists_unit_phase_norm_sub_sq_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖u - z • v‖ ^ 2 ≤ 2 * (1 - ‖inner ℂ v u‖ ^ 2) := by
  let a := inner ℂ v u
  have ha : ‖a‖ ≤ 1 := by
    simpa only [a, hu, hv, one_mul] using norm_inner_le_norm v u
  have hphase : ∃ z : ℂ, ‖z‖ = 1 ∧ inner ℂ (z • v) u = (‖a‖ : ℂ) := by
    by_cases hz : a = 0
    · refine ⟨1, norm_one, ?_⟩
      simpa only [one_smul] using (show a = (‖a‖ : ℂ) by rw [hz]; simp)
    · let z : ℂ := a / (‖a‖ : ℂ)
      have han : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have hanc : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr han
      have hnz : ‖z‖ = 1 := by
        simp only [z, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg a), div_self han]
      refine ⟨z, hnz, ?_⟩
      rw [inner_smul_left]
      change star z * a = (‖a‖ : ℂ)
      simp only [z, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_eq_mul_div, Complex.conj_mul']
      field_simp
  obtain ⟨z, hz, hzinner⟩ := hphase
  refine ⟨z, hz, ?_⟩
  have hnv : ‖z • v‖ = 1 := by rw [norm_smul, hz, hv, one_mul]
  have hn : ‖u - z • v‖ ^ 2 = 2 - 2 * ‖a‖ := by
    rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ), hnv, hu, hzinner]
    change (1 : ℝ) ^ 2 - 2 * ‖a‖ + 1 ^ 2 = 2 - 2 * ‖a‖
    ring
  change ‖u - z • v‖ ^ 2 ≤ 2 * (1 - ‖a‖ ^ 2)
  rw [hn]
  nlinarith [norm_nonneg a, mul_nonneg (norm_nonneg a) (sub_nonneg.mpr ha)]

end InfiniteZero
