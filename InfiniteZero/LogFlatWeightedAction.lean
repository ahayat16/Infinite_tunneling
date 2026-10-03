import InfiniteZero.LogFlatIntegral

/-!
# Log-flat gain after a weighted action comparison

A positive linear remainder in the normal action absorbs any weight already
included in the comparison. The threshold is uniform in the normal variable
and the three action values; the zero endpoint is included.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

theorem eventually_logFlat_weighted_action_le {β β₁ tStar a : ℝ}
    (hβ₁ : 0 < β₁) (hgap : β₁ < β) (hStar : 0 < tStar) (ha : 0 < a) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ t : ℝ, 0 ≤ t → ∀ w J J₀ : ℝ,
      w - (J - J₀) ≤ -a * t →
      Real.exp (w / h) * logFlat β tStar t * Real.exp (-J / h) ≤
        Real.exp (-J₀ / h) * Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_logFlat_laplace_le (hβ₁.trans hgap) hStar ha (sub_pos.mpr hgap)]
    with h hh hlog
  have hhp : 0 < h := hh
  intro t _ht w J J₀ hgain
  by_cases ht : 0 < t
  · rw [logFlat_of_pos β tStar ht, ← Real.exp_add, ← Real.exp_add]
    have hgainh := div_le_div_of_nonneg_right hgain hhp.le
    have hexponent : w / h + -β * (Real.log (tStar / t)) ^ 2 + -J / h ≤
        -J₀ / h + (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) := by
      convert add_le_add_right hgainh
        (-J₀ / h - β * (Real.log (tStar / t)) ^ 2) using 1 <;> ring
    calc
      _ ≤ Real.exp (-J₀ / h + (-β * (Real.log (tStar / t)) ^ 2 - a * t / h)) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp (-J₀ / h) *
          Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) :=
        Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [sub_sub_cancel] using hlog a le_rfl t ht)
        (Real.exp_pos _).le
  · rw [logFlat_of_nonpos β tStar (le_of_not_gt ht), mul_zero, zero_mul]
    positivity

end InfiniteZero
