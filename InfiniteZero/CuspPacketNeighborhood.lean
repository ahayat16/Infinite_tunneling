import InfiniteZero.CuspWeightedActionGain

/-!
# Fixed nested neighborhoods of the closed cusp supports

Two radial annuli contain both closed cusp supports, with a compact inner
closure inside the outer annulus. The explicit positive semiclassical scale
keeps every ball of radius `2h` around the inner closure inside the outer
neighborhood. All radii are fixed by the potential parameters.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

/-- A fixed outer radius with a two-unit margin around the cusp supports. -/
def cuspPacketRadius (p : CuspParameters) : ℝ :=
  max p.R p.cuspSupportRadius + 2

/-- The outer open annulus used for the local response equation. -/
def cuspPacketNeighborhood (p : CuspParameters) : Set Plane :=
  {x | ‖x‖ ∈ Ioo (p.R / 2) p.cuspPacketRadius}

/-- The smaller open annulus still contains the closed cusp supports. -/
def cuspPacketInnerNeighborhood (p : CuspParameters) : Set Plane :=
  {x | ‖x‖ ∈ Ioo (3 * p.R / 4) (p.cuspPacketRadius - 1)}

theorem cuspPacketRadius_pos {p : CuspParameters} (hp : p.BasicConditions) :
    0 < p.cuspPacketRadius := by
  have hR := hp.radius_pos
  have hmax := le_max_left p.R p.cuspSupportRadius
  dsimp [cuspPacketRadius]
  linarith

theorem half_radius_le_cuspPacketRadius {p : CuspParameters} (hp : p.BasicConditions) :
    p.R / 2 ≤ p.cuspPacketRadius := by
  have hR := hp.radius_pos
  have hmax := le_max_left p.R p.cuspSupportRadius
  dsimp [cuspPacketRadius]
  linarith

theorem isOpen_cuspPacketNeighborhood (p : CuspParameters) :
    IsOpen p.cuspPacketNeighborhood :=
  isOpen_Ioo.preimage continuous_norm

theorem isOpen_cuspPacketInnerNeighborhood (p : CuspParameters) :
    IsOpen p.cuspPacketInnerNeighborhood :=
  isOpen_Ioo.preimage continuous_norm

/-- The inner closure has closed radial bounds, including its boundary. -/
theorem closure_cuspPacketInnerNeighborhood_norm_bounds (p : CuspParameters) :
    closure p.cuspPacketInnerNeighborhood ⊆
      {x : Plane | ‖x‖ ∈ Icc (3 * p.R / 4) (p.cuspPacketRadius - 1)} := by
  apply closure_minimal
  · intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  · exact isClosed_Icc.preimage continuous_norm

theorem closure_cuspPacketInnerNeighborhood_subset {p : CuspParameters}
    (hp : p.BasicConditions) :
    closure p.cuspPacketInnerNeighborhood ⊆ p.cuspPacketNeighborhood := by
  intro x hx
  have hb := closure_cuspPacketInnerNeighborhood_norm_bounds p hx
  exact ⟨by linarith [hp.radius_pos, hb.1], by linarith [hb.2]⟩

theorem cuspPacketInnerNeighborhood_subset {p : CuspParameters}
    (hp : p.BasicConditions) :
    p.cuspPacketInnerNeighborhood ⊆ p.cuspPacketNeighborhood :=
  subset_closure.trans (closure_cuspPacketInnerNeighborhood_subset hp)

theorem cuspPacketNeighborhood_norm_bounds (p : CuspParameters) :
    p.cuspPacketNeighborhood ⊆
      {x : Plane | ‖x‖ ∈ Icc (p.R / 2) p.cuspPacketRadius} :=
  fun _ hx => ⟨hx.1.le, hx.2.le⟩

theorem cuspPacketNeighborhood_subset_closedBall (p : CuspParameters) :
    p.cuspPacketNeighborhood ⊆ Metric.closedBall (0 : Plane) p.cuspPacketRadius := by
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le

/-- Relative compactness is proved directly inside a fixed planar ball. -/
theorem isCompact_closure_cuspPacketInnerNeighborhood (p : CuspParameters) :
    IsCompact (closure p.cuspPacketInnerNeighborhood) := by
  apply (isCompact_closedBall (0 : Plane) p.cuspPacketRadius).of_isClosed_subset
    isClosed_closure
  intro x hx
  have hb := (closure_cuspPacketInnerNeighborhood_norm_bounds p hx).2
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith

theorem cuspPlus_tsupport_subset_cuspPacketInnerNeighborhood {p : CuspParameters}
    (hp : p.BasicConditions) : tsupport p.cuspPlus ⊆ p.cuspPacketInnerNeighborhood := by
  intro x hx
  have hr := cuspPlus_tsupport_norm_bounds hp hx
  have hmax := le_max_right p.R p.cuspSupportRadius
  refine ⟨by linarith [hp.radius_pos, hr.1], ?_⟩
  dsimp [cuspPacketRadius]
  linarith [hr.2]

theorem cuspMinus_tsupport_subset_cuspPacketInnerNeighborhood {p : CuspParameters}
    (hp : p.BasicConditions) : tsupport p.cuspMinus ⊆ p.cuspPacketInnerNeighborhood := by
  intro x hx
  have hr := cuspMinus_tsupport_norm_bounds hp hx
  have hmax := le_max_right p.R p.cuspSupportRadius
  refine ⟨by linarith [hp.radius_pos, hr.1], ?_⟩
  dsimp [cuspPacketRadius]
  linarith [hr.2]

theorem atomicPerturbation_tsupport_subset_cuspPacketInnerNeighborhood
    {p : CuspParameters} (hp : p.BasicConditions) :
    tsupport p.atomicPerturbation ⊆ p.cuspPacketInnerNeighborhood := by
  intro x hx
  rcases atomicPerturbation_tsupport_subset_cusps p hx with hplus | hminus
  · exact cuspPlus_tsupport_subset_cuspPacketInnerNeighborhood hp hplus
  · exact cuspMinus_tsupport_subset_cuspPacketInnerNeighborhood hp hminus

/-- An explicit uniform scale for balls around the full inner closure. -/
def cuspPacketBallScale (p : CuspParameters) : ℝ := min (p.R / 16) (1 / 4)

theorem cuspPacketBallScale_pos {p : CuspParameters} (hp : p.BasicConditions) :
    0 < p.cuspPacketBallScale :=
  lt_min (div_pos hp.radius_pos (by norm_num)) (by norm_num)

/-- The same ball radius works at every point of the compact inner closure,
including its two annular boundary circles. -/
theorem cuspPacket_closedBall_subset {p : CuspParameters} (hp : p.BasicConditions)
    {x : Plane} (hx : x ∈ closure p.cuspPacketInnerNeighborhood)
    {h : ℝ} (hh : h ∈ Ioc 0 p.cuspPacketBallScale) :
    Metric.closedBall x (2 * h) ⊆ p.cuspPacketNeighborhood := by
  intro y hy
  have hxrad := closure_cuspPacketInnerNeighborhood_norm_bounds p hx
  have hdist : ‖y - x‖ ≤ 2 * h := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  have hdiff := abs_le.mp ((abs_norm_sub_norm_le y x).trans hdist)
  have hhR : h ≤ p.R / 16 := hh.2.trans (min_le_left _ _)
  have hh1 : h ≤ (1 / 4 : ℝ) := hh.2.trans (min_le_right _ _)
  exact ⟨by linarith [hp.radius_pos, hxrad.1, hdiff.1],
    by linarith [hxrad.2, hdiff.2]⟩

/-- The potential fixes the positive local scale before the center and
semiclassical parameter are chosen. -/
theorem exists_cuspPacket_uniform_ball_radius {p : CuspParameters}
    (hp : p.BasicConditions) :
    ∃ h₀ > 0, ∀ x ∈ closure p.cuspPacketInnerNeighborhood,
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        Metric.closedBall x (2 * h) ⊆ p.cuspPacketNeighborhood := by
  refine ⟨p.cuspPacketBallScale, cuspPacketBallScale_pos hp, ?_⟩
  intro x hx h hh hsmall
  exact cuspPacket_closedBall_subset hp hx ⟨hh, hsmall⟩

end InfiniteZero.CuspParameters
