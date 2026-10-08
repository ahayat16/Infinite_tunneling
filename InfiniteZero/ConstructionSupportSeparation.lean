import InfiniteZero.ConstructionCuspSmoothAway

/-!
# Pairwise separation of the closed component supports

The elementary width condition already places the entire upper cusp above
its tip and the reflected cusp below its tip. This separates their closed
supports, as well as separating both from the radial core.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

theorem core_tsupport_subset_closedBall (p : CuspParameters) :
    tsupport p.core ⊆ Metric.closedBall 0 p.r₀ := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (by simp [core, not_lt.mpr (le_of_not_ge hn)])

theorem cuspPlus_tsupport_norm_lower (p : CuspParameters) {x : Plane}
    (hx : x ∈ tsupport p.cuspPlus) : p.R / 2 ≤ ‖x‖ := by
  have ht := (cuspPlus_tsupport_subset_quadratic p hx).1
  linarith [normalCoordinate_le_norm p x]

theorem core_cuspPlus_tsupport_disjoint {p : CuspParameters} (h : p.BasicConditions) :
    Disjoint (tsupport p.core) (tsupport p.cuspPlus) := by
  apply Set.disjoint_left.mpr
  intro x hc hq
  have hc' := core_tsupport_subset_closedBall p hc
  rw [Metric.mem_closedBall, dist_zero_right] at hc'
  have hq' := cuspPlus_tsupport_norm_lower p hq
  linarith [h.radius_large, h.r₀_pos]

theorem cuspMinus_tsupport_norm_lower (p : CuspParameters) {x : Plane}
    (hx : x ∈ tsupport p.cuspMinus) : p.R / 2 ≤ ‖x‖ := by
  have href : reflection x ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
  simpa only [norm_reflection] using cuspPlus_tsupport_norm_lower p href

theorem core_cuspMinus_tsupport_disjoint {p : CuspParameters} (h : p.BasicConditions) :
    Disjoint (tsupport p.core) (tsupport p.cuspMinus) := by
  apply Set.disjoint_left.mpr
  intro x hc hq
  have hc' := core_tsupport_subset_closedBall p hc
  rw [Metric.mem_closedBall, dist_zero_right] at hc'
  have hq' := cuspMinus_tsupport_norm_lower p hq
  linarith [h.radius_large, h.r₀_pos]

theorem cuspPlus_support_vertical {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ Function.support p.cuspPlus) :
    Real.sqrt 3 * p.R / 2 ≤ x 1 := by
  have hc : 0 < p.normalCoordinate x ∧ p.normalCoordinate x < p.t₀ ∧
      |p.tangentCoordinate x / p.normalCoordinate x ^ 2| < p.s₀ := by
    by_contra hn
    exact hx (by simp [cuspPlus, hn])
  have ht2 : 0 < p.normalCoordinate x ^ 2 := sq_pos_of_pos hc.1
  have hu : p.tangentCoordinate x < p.s₀ * p.normalCoordinate x ^ 2 := by
    have huabs : |p.tangentCoordinate x| < p.s₀ * p.normalCoordinate x ^ 2 := by
      apply (div_lt_iff₀ ht2).mp
      simpa only [abs_div, abs_of_pos ht2] using hc.2.2
    exact lt_of_le_of_lt (le_abs_self _) huabs
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 3 := by norm_num
  have hst₀ : p.s₀ * p.t₀ ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hsqrt (mul_nonneg h.s₀_pos.le h.t₀_pos.le)
    nlinarith [h.width_small]
  have hst : p.s₀ * p.normalCoordinate x ≤ Real.sqrt 3 := by
    have hm := mul_le_mul_of_nonneg_left hc.2.1.le h.s₀_pos.le
    linarith
  have hut : p.tangentCoordinate x ≤ Real.sqrt 3 * p.normalCoordinate x := by
    have hm := mul_le_mul_of_nonneg_right hst hc.1.le
    nlinarith
  have he := congrArg (fun y : Plane => y 1) (cuspFrame_reconstruction p x)
  simp [cuspTip, cuspNormal, cuspTangent] at he
  linarith

theorem cuspPlus_tsupport_vertical {p : CuspParameters} (h : p.BasicConditions) :
    tsupport p.cuspPlus ⊆ {x | Real.sqrt 3 * p.R / 2 ≤ x 1} := by
  exact closure_minimal (fun _ hx => cuspPlus_support_vertical h hx)
    (isClosed_le continuous_const
      (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (i := (1 : Fin 2)) 2).continuous)

theorem cuspMinus_tsupport_vertical {p : CuspParameters} (h : p.BasicConditions) :
    tsupport p.cuspMinus ⊆ {x | x 1 ≤ -(Real.sqrt 3 * p.R / 2)} := by
  apply closure_minimal
  · intro x hx
    change x 1 ≤ -(Real.sqrt 3 * p.R / 2)
    have hy := cuspPlus_support_vertical h (x := reflection x) hx
    simp [reflection] at hy
    change Real.sqrt 3 * p.R / 2 ≤ -x 1 at hy
    linarith
  · exact isClosed_le
      (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (i := (1 : Fin 2)) 2).continuous
      continuous_const

theorem cuspPlus_cuspMinus_tsupport_disjoint {p : CuspParameters} (h : p.BasicConditions) :
    Disjoint (tsupport p.cuspPlus) (tsupport p.cuspMinus) := by
  apply Set.disjoint_left.mpr
  intro x hp hm
  have hpos : 0 < Real.sqrt 3 * p.R := mul_pos (by positivity) h.radius_pos
  have hp' := cuspPlus_tsupport_vertical h hp
  have hm' := cuspMinus_tsupport_vertical h hm
  dsimp only [Set.mem_setOf_eq] at hp' hm'
  linarith

end InfiniteZero.CuspParameters
