import InfiniteZero.Geometry
import InfiniteZero.BridgeAction

/-!
# The inactive same-cusp action has a uniform positive margin at the tips

The explicit margin is independent of the positive energy. Identification of
this explicit action with the Landau decay rate, neighborhoods of the tips,
and the other inactive source pairings remain separate tasks.
-/

noncomputable section

namespace InfiniteZero.Geometry

theorem length_bridge_same_plus_gt {R L : ℝ} (hR : 0 < R) (hL : R < 2 * L) :
    activeDistance R L < length (bridge L (tipPlus R) (tipPlus R)) := by
  rw [length, sqNorm_bridge_same_plus]
  apply (Real.lt_sqrt (activeDistance_pos hL).le).mpr
  nlinarith [sq_pos_of_pos hR]

theorem length_bridge_same_minus_gt {R L : ℝ} (hR : 0 < R) (hL : R < 2 * L) :
    activeDistance R L < length (bridge L (tipMinus R) (tipMinus R)) := by
  rw [length, sqNorm_bridge_same_minus]
  apply (Real.lt_sqrt (activeDistance_pos hL).le).mpr
  nlinarith [sq_pos_of_pos hR]

theorem same_cusp_action_gap_pos {b E R L : ℝ} (hb : b ≠ 0) (hE : 0 < E)
    (hR : 0 < R) (hL : R < 2 * L) :
    0 < bridgeAction b E (length (bridge L (tipPlus R) (tipPlus R))) -
      bridgeAction b E (activeDistance R L) := by
  exact sub_pos.mpr (strictMono_bridgeAction hb hE (length_bridge_same_plus_gt hR hL))

theorem same_cusp_action_gap_lower {b E R L : ℝ} (hb : b ≠ 0) (hE : 0 < E)
    (hR : 0 < R) (hL : R < 2 * L) :
    Real.sqrt E * (length (bridge L (tipPlus R) (tipPlus R)) - activeDistance R L) ≤
      bridgeAction b E (length (bridge L (tipPlus R) (tipPlus R))) -
        bridgeAction b E (activeDistance R L) :=
  bridgeAction_sub_ge hb hE (length_bridge_same_plus_gt hR hL).le

/-- The exact same-cusp margin of blueprint P2.6, uniform for every `E > 0`. -/
theorem same_cusp_action_gap_ge {b E R L : ℝ} (hb : 0 < b) (hE : 0 < E)
    (hR : 0 < R) (hL : R < 2 * L) :
    3 * b * R ^ 2 / 4 ≤
      bridgeAction b E (length (bridge L (tipPlus R) (tipPlus R))) -
        bridgeAction b E (activeDistance R L) := by
  have hsq : length (bridge L (tipPlus R) (tipPlus R)) ^ 2 =
      activeDistance R L ^ 2 + 3 * R ^ 2 := by
    rw [length, sqNorm_bridge_same_plus, Real.sq_sqrt (by positivity)]
  have hbound := bridgeAction_sub_ge_quadratic hb hE (activeDistance_pos hL).le
    (length_bridge_same_plus_gt hR hL).le
  rw [hsq] at hbound
  nlinarith only [hbound]

theorem same_cusp_minus_action_gap_ge {b E R L : ℝ} (hb : 0 < b) (hE : 0 < E)
    (hR : 0 < R) (hL : R < 2 * L) :
    3 * b * R ^ 2 / 4 ≤
      bridgeAction b E (length (bridge L (tipMinus R) (tipMinus R))) -
        bridgeAction b E (activeDistance R L) := by
  have he : length (bridge L (tipMinus R) (tipMinus R)) =
      length (bridge L (tipPlus R) (tipPlus R)) := by
    simp only [length, sqNorm_bridge_same_minus, sqNorm_bridge_same_plus]
  rw [he]
  exact same_cusp_action_gap_ge hb hE hR hL

end InfiniteZero.Geometry
