import InfiniteZero.CuspWeightedActionGain
import InfiniteZero.InactiveSupportGaps
import InfiniteZero.HoppingIntegrability
import InfiniteZero.LandauKernelExactActionUpper

/-!
# Exact-action upper bounds on the two active cusp pairs

The outgoing horizontal geometry places the bridge radius above `2L-R`.
Its upper bound is fixed by the compact cusp supports. The uniform Landau
bound therefore retains the full action at `2L-R`, with only the factor
`h⁻²`. No positive loss in the action is introduced.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

theorem cuspCross_bridge_distance_ge_activeDistance {p : CuspParameters}
    (hp : p.BasicConditions) (L : ℝ) {z w : Plane}
    (hz : z ∈ tsupport p.cuspPlus) (hw : w ∈ tsupport p.cuspMinus) :
    Geometry.activeDistance p.R L ≤ ‖z + w - 2 • displacement L‖ := by
  have hzt := (cuspPlus_tsupport_subset_quadratic p hz).1
  have href : reflection w ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hw
  have hwt := (cuspPlus_tsupport_subset_quadratic p href).1
  have hzh := cuspPlus_tsupport_horizontal hp hz
  have hwh := (cuspMinus_tsupport_outgoing_bounds hp hw).1
  have hb := bridge_distance_ge_horizontal z w L
  dsimp [Geometry.activeDistance]
  linarith

/-- A positive fixed radius interval covers both ordered active pairs,
including the cusp tips and all boundaries of the closed supports. -/
theorem activeCross_bridge_distance_bounds {p : CuspParameters}
    (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) {z w : Plane}
    (hzw : (z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspMinus) ∨
      (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspPlus)) :
    0 < Geometry.activeDistance p.R L ∧
      ‖z + w - 2 • displacement L‖ ∈
        Icc (Geometry.activeDistance p.R L) (2 * (L + p.cuspSupportRadius)) := by
  have hLp : 0 ≤ L := by linarith [hp.radius_pos]
  refine ⟨by simpa only [Geometry.activeDistance, sub_pos] using hL, ?_⟩
  rcases hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · exact ⟨cuspCross_bridge_distance_ge_activeDistance hp L hz hw,
      (bridge_distance_annulus hLp (cuspPlus_tsupport_norm_bounds hp hz).2
        (cuspMinus_tsupport_norm_bounds hp hw).2).2⟩
  · constructor
    · simpa only [add_comm w z] using
        cuspCross_bridge_distance_ge_activeDistance hp L hw hz
    · exact (bridge_distance_annulus hLp (cuspMinus_tsupport_norm_bounds hp hz).2
        (cuspPlus_tsupport_norm_bounds hp hw).2).2

/-- The constant is chosen before the energy, `h`, and both source points.
The two active orientations share the same exact-action bound. -/
theorem exists_activeCrossKernel_exact_action_upper {p : CuspParameters}
    (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ h > 0, h ≤ 1 → ∀ z w : Plane,
      ((z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspMinus) ∨
        (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspPlus)) →
      landauKernel p.b h E ‖z + w - 2 • displacement L‖ ≤
        C * (h ^ 2)⁻¹ *
          Real.exp (-bridgeAction p.b E (Geometry.activeDistance p.R L) / h) := by
  have hD : 0 < Geometry.activeDistance p.R L := by
    simpa only [Geometry.activeDistance, sub_pos] using hL
  have ha : 0 ≤ p.cuspSupportRadius := by
    unfold cuspSupportRadius
    have ht := hp.t₀_pos
    have hs := hp.s₀_pos
    positivity
  have hDR : Geometry.activeDistance p.R L ≤ 2 * (L + p.cuspSupportRadius) := by
    dsimp [Geometry.activeDistance]
    linarith [hp.radius_pos]
  obtain ⟨C, hC, hbound⟩ := exists_uniform_landauKernel_exact_action_upper hp.b_pos
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hD hDR
  refine ⟨C, hC, ?_⟩
  intro E hE h hh hh1 z w hzw
  have hr := (activeCross_bridge_distance_bounds hp hL hzw).2
  have hEp : 0 < E := lt_of_lt_of_le (by norm_num) hE.1
  apply (hbound E hE _ hr h hh hh1).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (inv_nonneg.mpr (sq_nonneg h)))
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (neg_le_neg ((strictMono_bridgeAction hp.b_pos.ne' hEp).monotone hr.1)) hh.le

end InfiniteZero.CuspParameters
