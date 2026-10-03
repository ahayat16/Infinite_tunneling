import InfiniteZero.BridgeAction
import Mathlib.Analysis.Calculus.Taylor

/-! Uniform second-order radial control of the explicit action. The bound
is independent of the positive energy and of both real radii. -/

noncomputable section
open Set
open scoped Interval

namespace InfiniteZero

theorem contDiff_bridgeAction (b : ℝ) {E : ℝ} (hE : 0 < E) (n : ℕ∞) :
    ContDiff ℝ n (bridgeAction b E) := by
  have hrad : ContDiff ℝ n (fun r : ℝ => b ^ 2 * r ^ 2 + 4 * E) := by fun_prop
  have hroot := hrad.sqrt (fun r => by positivity : ∀ r : ℝ, b ^ 2 * r ^ 2 + 4 * E ≠ 0)
  unfold bridgeAction
  exact ((contDiff_id.div_const 4).mul hroot).add
    (contDiff_const.mul (((contDiff_const.mul contDiff_id).div_const (2 * Real.sqrt E)).arsinh))

theorem abs_deriv2_bridgeAction_le {b E : ℝ} (hb : 0 < b) (hE : 0 < E) (r : ℝ) :
    |deriv (deriv (bridgeAction b E)) r| ≤ b / 2 := by
  have hrad : 0 < b ^ 2 * r ^ 2 + 4 * E := by positivity
  have hroot : 0 < Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) := Real.sqrt_pos.mpr hrad
  have hs : b * |r| ≤ Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, sq_abs]
    linarith
  rw [deriv2_bridgeAction hb.ne' hE, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg b), abs_of_pos (mul_pos (by norm_num) hroot)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hroot)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hb.le]

theorem exists_bridgeAction_quadratic_point {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E)
    (r s : ℝ) :
    ∃ ξ ∈ uIcc r s, bridgeAction b E s - bridgeAction b E r -
      deriv (bridgeAction b E) r * (s - r) =
        deriv (deriv (bridgeAction b E)) ξ / 2 * (s - r) ^ 2 := by
  by_cases hrs : r = s
  · subst s
    exact ⟨r, by simp, by simp⟩
  have hminmax : min r s < max r s := by
    rcases lt_or_gt_of_ne hrs with h | h <;> simp [h.le, h]
  have hu := uniqueDiffOn_Icc hminmax
  have hderiv : derivWithin (bridgeAction b E) (uIcc r s) r = deriv (bridgeAction b E) r :=
    (differentiable_bridgeAction hb hE r).hasDerivAt.hasDerivWithinAt.derivWithin
      (hu r left_mem_uIcc)
  obtain ⟨ξ, hξ, ht⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hrs ((contDiff_bridgeAction b hE 2).contDiffOn)
  refine ⟨ξ, Ioo_subset_Icc_self hξ, ?_⟩
  have ht' : bridgeAction b E s -
      (bridgeAction b E r + deriv (bridgeAction b E) r * (s - r)) =
        deriv (deriv (bridgeAction b E)) ξ * (s - r) ^ 2 / 2 := by
    simpa [taylorWithinEval_succ, iteratedDerivWithin_one, hderiv,
      iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial, smul_eq_mul, mul_comm] using ht
  linear_combination ht'

/-- A global Taylor estimate with an explicit constant, uniform for all E>0. -/
theorem abs_bridgeAction_sub_linear_le {b E : ℝ} (hb : 0 < b) (hE : 0 < E)
    (r s : ℝ) :
    |bridgeAction b E s - bridgeAction b E r - deriv (bridgeAction b E) r * (s - r)| ≤
      b / 4 * (s - r) ^ 2 := by
  obtain ⟨ξ, _, he⟩ := exists_bridgeAction_quadratic_point hb.ne' hE r s
  rw [he, abs_mul, abs_div, abs_of_nonneg (sq_nonneg (s - r))]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (b / 2) / 2 * (s - r) ^ 2 := by
      gcongr
      exact abs_deriv2_bridgeAction_le hb hE ξ
    _ = _ := by ring

end InfiniteZero
