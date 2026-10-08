import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Elementary absorption estimates used for the actual Schur residual. -/

namespace InfiniteZero

theorem schur_residual_exponential_bound {K d g coupling r : ℝ}
    (hK : 0 ≤ K) (hd : 0 ≤ d) (hg : 0 < g) (hc : 0 < coupling)
    (hr0 : 0 ≤ r) (hr : r ≤ K * coupling * Real.exp (-d * coupling)) :
    r + r ^ 2 / (g * coupling) ≤
      (K + K ^ 2 / g) * coupling * Real.exp (-d * coupling) := by
  let q := Real.exp (-d * coupling)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hc.le)
  have hq2 : q ^ 2 ≤ q := by nlinarith only [hq0, hq1]
  have hr2 : r ^ 2 ≤ (K * coupling * q) ^ 2 :=
    (sq_le_sq₀ hr0 (mul_nonneg (mul_nonneg hK hc.le) hq0)).mpr hr
  have hs : r ^ 2 ≤ K ^ 2 * coupling ^ 2 * q := by
    have h := mul_le_mul_of_nonneg_left hq2 (mul_nonneg (sq_nonneg K) (sq_nonneg coupling))
    nlinarith only [hr2, h]
  have hdiv : r ^ 2 / (g * coupling) ≤ K ^ 2 / g * coupling * q := by
    apply (div_le_iff₀ (mul_pos hg hc)).mpr
    have heq : K ^ 2 / g * coupling * q * (g * coupling) =
        K ^ 2 * coupling ^ 2 * q := by field_simp
    rw [heq]
    exact hs
  change r + r ^ 2 / (g * coupling) ≤ (K + K ^ 2 / g) * coupling * q
  nlinarith only [hr, hdiv]

/-- Losing half the exponential rate absorbs the linear prefactor, with
an explicit constant and no asymptotic hypothesis. -/
theorem linear_mul_exp_neg_le_half {d : ℝ} (hd : 0 < d) (coupling : ℝ) :
    coupling * Real.exp (-d * coupling) ≤
      (2 / d) * Real.exp (-(d / 2) * coupling) := by
  have hbase : (d / 2 * coupling) * Real.exp (-(d / 2 * coupling)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hm : 0 ≤ (2 / d) * Real.exp (-(d / 2) * coupling) :=
    mul_nonneg (div_nonneg (by norm_num) hd.le) (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_right hbase hm
  have heq : (d / 2 * coupling) * Real.exp (-(d / 2 * coupling)) *
      ((2 / d) * Real.exp (-(d / 2) * coupling)) =
      coupling * Real.exp (-d * coupling) := by
    calc
      _ = coupling * (Real.exp (-(d / 2 * coupling)) *
          Real.exp (-(d / 2) * coupling)) := by field_simp
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  simpa only [heq, one_mul] using h

end InfiniteZero
