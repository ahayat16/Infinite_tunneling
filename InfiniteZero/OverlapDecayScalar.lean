import InfiniteZero.LogFlat

/-! Scalar conversion of a squared overlap bound and its vanishing rate. -/

noncomputable section
open Filter
open scoped Topology

namespace InfiniteZero

theorem le_overlap_decay_of_sq_le {x C d coupling : ℝ}
    (hc : 0 < coupling) (hC : 0 ≤ C)
    (hbound : x ^ 2 ≤ 4 * ((C / coupling ^ 2) * Real.exp (-2 * d * coupling))) :
    |x| ≤ (2 * Real.sqrt C) / coupling * Real.exp (-d * coupling) := by
  have hexp : Real.exp (-2 * d * coupling) = Real.exp (-d * coupling) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hid : 4 * ((C / coupling ^ 2) * Real.exp (-2 * d * coupling)) =
      ((2 * Real.sqrt C) / coupling * Real.exp (-d * coupling)) ^ 2 := by
    rw [hexp]
    simp only [mul_pow, div_pow, Real.sq_sqrt hC]
    ring
  apply (sq_le_sq₀ (abs_nonneg x) (by positivity)).mp
  simpa only [sq_abs, hid] using hbound

theorem tendsto_overlap_decay (C : ℝ) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun coupling : ℝ => C / coupling * Real.exp (-d * coupling))
      atTop (𝓝 0) := by
  have he := Real.tendsto_exp_atBot.comp
    ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop_of_neg
      (neg_neg_of_pos hd))
  simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).const_mul C).mul he

end InfiniteZero
