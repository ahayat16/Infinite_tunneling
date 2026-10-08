import InfiniteZero.ConstructionCuspBounds
import InfiniteZero.SeparationCertificate

/-!
# The seven inactive action gaps on the full closed supports

This proves T5.5 directly for the constructed potential. The bridge energy `E`
and incoming reference energy `E₀` remain distinct. The separation certificate
gives a margin `32 δ` for the core and mixed cells and the squared-distance
bound gives `48 δ` for the same-cusp cells. No source estimate or convergence
of an atomic energy is assumed.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

def activeReferenceAction (p : CuspParameters) (L E E₀ : ℝ) : ℝ :=
  2 * bridgeAction p.b E₀ p.R + bridgeAction p.b E (Geometry.activeDistance p.R L)

theorem core_tsupport_horizontal (p : CuspParameters) {x : Plane}
    (hx : x ∈ tsupport p.core) : x 0 ≤ p.r₀ := by
  have hr := core_tsupport_subset_closedBall p hx
  rw [Metric.mem_closedBall, dist_zero_right] at hr
  have hn : |x 0| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (0 : Fin 2)
  exact (le_abs_self _).trans (hn.trans hr)

/-- Both cusps have the same horizontal bound, including their boundaries. -/
theorem cusp_tsupport_horizontal_le {p : CuspParameters} (h : p.BasicConditions) {x : Plane}
    (hx : x ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus) : x 0 ≤ p.R / 2 := by
  rcases hx with hx | hx
  · have ht := (cuspPlus_tsupport_subset_quadratic p hx).1
    linarith [cuspPlus_tsupport_horizontal h hx]
  · have href : reflection x ∈ tsupport p.cuspPlus :=
      tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
    have ht := (cuspPlus_tsupport_subset_quadratic p href).1
    linarith [(cuspMinus_tsupport_outgoing_bounds h hx).1]

/-- A horizontal coordinate bound already supplies a lower bound for the
full bridge distance; positivity is not needed for this elementary step. -/
theorem bridge_norm_ge_horizontal (L : ℝ) (z w : Plane) :
    2 * L - z 0 - w 0 ≤ ‖z + w - 2 • displacement L‖ := by
  have hc := (neg_le_abs ((z + w - 2 • displacement L) 0)).trans
    (show |(z + w - 2 • displacement L) 0| ≤ ‖z + w - 2 • displacement L‖ from
      by simpa only [Real.norm_eq_abs] using
        PiLp.norm_apply_le (z + w - 2 • displacement L) (0 : Fin 2))
  have he : (z + w - 2 • displacement L) 0 = z 0 + w 0 - 2 * L := by
    simp [displacement, coordinateVector]
  rw [he] at hc
  linarith

theorem core_core_distance (p : CuspParameters) (L : ℝ) {z w : Plane}
    (hz : z ∈ tsupport p.core) (hw : w ∈ tsupport p.core) :
    Geometry.activeDistance p.R L + p.coreCoreIncrement ≤ ‖z + w - 2 • displacement L‖ := by
  have hz₀ := core_tsupport_horizontal p hz
  have hw₀ := core_tsupport_horizontal p hw
  have hb := bridge_norm_ge_horizontal L z w
  dsimp [Geometry.activeDistance, coreCoreIncrement]
  linarith

theorem core_cusp_distance {p : CuspParameters} (h : p.BasicConditions) (L : ℝ) {z w : Plane}
    (hz : z ∈ tsupport p.core) (hw : w ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus) :
    Geometry.activeDistance p.R L + p.coreCuspIncrement ≤ ‖z + w - 2 • displacement L‖ := by
  have hz₀ := core_tsupport_horizontal p hz
  have hw₀ := cusp_tsupport_horizontal_le h hw
  have hb := bridge_norm_ge_horizontal L z w
  dsimp [Geometry.activeDistance, coreCuspIncrement]
  linarith

theorem cusp_core_distance {p : CuspParameters} (h : p.BasicConditions) (L : ℝ) {z w : Plane}
    (hz : z ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus) (hw : w ∈ tsupport p.core) :
    Geometry.activeDistance p.R L + p.coreCuspIncrement ≤ ‖z + w - 2 • displacement L‖ := by
  simpa only [add_comm z w] using core_cusp_distance h L hw hz

theorem bridge_norm_sq (L : ℝ) (z w : Plane) :
    ‖z + w - 2 • displacement L‖ ^ 2 =
      (z 0 + w 0 - 2 * L) ^ 2 + (z 1 + w 1) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, displacement, coordinateVector]

theorem same_cusp_distance_sq {p : CuspParameters} (h : p.BasicConditions) {L : ℝ}
    (hL : p.R ≤ 2 * L) {z w : Plane}
    (hzw : (z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspPlus) ∨
      (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspMinus)) :
    Geometry.activeDistance p.R L ^ 2 + 3 * p.R ^ 2 ≤ ‖z + w - 2 • displacement L‖ ^ 2 := by
  have hh : z 0 + w 0 ≤ p.R := by
    rcases hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
    · linarith [cusp_tsupport_horizontal_le h (Or.inl hz),
        cusp_tsupport_horizontal_le h (Or.inl hw)]
    · linarith [cusp_tsupport_horizontal_le h (Or.inr hz),
        cusp_tsupport_horizontal_le h (Or.inr hw)]
  have hD : 0 ≤ Geometry.activeDistance p.R L := by
    dsimp [Geometry.activeDistance]
    linarith
  have hhor : Geometry.activeDistance p.R L ≤ -(z 0 + w 0 - 2 * L) := by
    dsimp [Geometry.activeDistance]
    linarith
  have hhorSq := (sq_le_sq₀ hD (hD.trans hhor)).mpr hhor
  rw [neg_sq] at hhorSq
  have hsqrt : 0 ≤ Real.sqrt 3 * p.R := mul_nonneg (Real.sqrt_nonneg 3) h.radius_pos.le
  have hver : 3 * p.R ^ 2 ≤ (z 1 + w 1) ^ 2 := by
    rcases hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
    · have hy : Real.sqrt 3 * p.R ≤ z 1 + w 1 := by
        have hzv : Real.sqrt 3 * p.R / 2 ≤ z 1 := cuspPlus_tsupport_vertical h hz
        have hwv : Real.sqrt 3 * p.R / 2 ≤ w 1 := cuspPlus_tsupport_vertical h hw
        linarith
      have hySq := (sq_le_sq₀ hsqrt (hsqrt.trans hy)).mpr hy
      simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using hySq
    · have hy : Real.sqrt 3 * p.R ≤ -(z 1 + w 1) := by
        have hzv : z 1 ≤ -(Real.sqrt 3 * p.R / 2) := cuspMinus_tsupport_vertical h hz
        have hwv : w 1 ≤ -(Real.sqrt 3 * p.R / 2) := cuspMinus_tsupport_vertical h hw
        linarith
      have hySq := (sq_le_sq₀ hsqrt (hsqrt.trans hy)).mpr hy
      simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), neg_sq] using hySq
  rw [bridge_norm_sq]
  exact add_le_add hhorSq hver

theorem same_cusp_action_gap {p : CuspParameters} (h : p.BasicConditions) {L E : ℝ}
    (hL : p.R ≤ 2 * L) (hE : 0 < E) {z w : Plane}
    (hzw : (z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspPlus) ∨
      (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspMinus)) :
    48 * p.hopMargin ≤ bridgeAction p.b E ‖z + w - 2 • displacement L‖ -
      bridgeAction p.b E (Geometry.activeDistance p.R L) := by
  have hsq := same_cusp_distance_sq h hL hzw
  have hD : 0 ≤ Geometry.activeDistance p.R L := sub_nonneg.mpr hL
  have hdist : Geometry.activeDistance p.R L ≤ ‖z + w - 2 • displacement L‖ :=
    (sq_le_sq₀ hD (norm_nonneg _)).mp (by nlinarith [sq_nonneg p.R])
  have hb := bridgeAction_sub_ge_quadratic h.b_pos hE hD hdist
  have hm := mul_le_mul_of_nonneg_left hsq (div_nonneg h.b_pos.le (by norm_num : (0 : ℝ) ≤ 4))
  dsimp [hopMargin]
  nlinarith only [hb, hm]

theorem SeparationCertificate.radius_lt {p : CuspParameters} (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) : p.R < L :=
  (lt_of_le_of_lt (le_max_right cert.supportRadius p.R) cert.separation).trans_le hL

theorem core_core_action_gap {p : CuspParameters} (h : p.BasicConditions)
    (cert : p.SeparationCertificate) {L E E₀ : ℝ} (hL : cert.L₀ ≤ L)
    (hE : 0 < E) (hE₀ : 0 < E₀) (hE₀max : E₀ ≤ 2) {z w : Plane}
    (hz : z ∈ tsupport p.core) (hw : w ∈ tsupport p.core) :
    p.activeReferenceAction L E E₀ + 32 * p.hopMargin ≤
      bridgeAction p.b E ‖z + w - 2 • displacement L‖ := by
  have hr := cert.core_core_reserve L hL E E₀ hE hE₀ hE₀max
  have hd := (strictMono_bridgeAction h.b_pos.ne' hE).monotone (core_core_distance p L hz hw)
  dsimp [channelReserve, actionIncrement] at hr
  dsimp [activeReferenceAction]
  linarith

theorem core_cusp_action_gap {p : CuspParameters} (h : p.BasicConditions)
    (cert : p.SeparationCertificate) {L E E₀ : ℝ} (hL : cert.L₀ ≤ L)
    (hE : 0 < E) (hE₀ : 0 < E₀) (hE₀max : E₀ ≤ 2) {z w : Plane}
    (hz : z ∈ tsupport p.core) (hw : w ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus) :
    p.activeReferenceAction L E E₀ + 32 * p.hopMargin ≤
      bridgeAction p.b E₀ p.R + bridgeAction p.b E ‖z + w - 2 • displacement L‖ := by
  have hr := cert.core_cusp_reserve L hL E E₀ hE hE₀ hE₀max
  have hd := (strictMono_bridgeAction h.b_pos.ne' hE).monotone (core_cusp_distance h L hz hw)
  dsimp [channelReserve, actionIncrement] at hr
  dsimp [activeReferenceAction]
  linarith

theorem cusp_core_action_gap {p : CuspParameters} (h : p.BasicConditions)
    (cert : p.SeparationCertificate) {L E E₀ : ℝ} (hL : cert.L₀ ≤ L)
    (hE : 0 < E) (hE₀ : 0 < E₀) (hE₀max : E₀ ≤ 2) {z w : Plane}
    (hz : z ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus) (hw : w ∈ tsupport p.core) :
    p.activeReferenceAction L E E₀ + 32 * p.hopMargin ≤
      bridgeAction p.b E₀ p.R + bridgeAction p.b E ‖z + w - 2 • displacement L‖ := by
  simpa only [add_comm z w] using core_cusp_action_gap h cert hL hE hE₀ hE₀max hw hz

theorem same_cusp_total_action_gap {p : CuspParameters} (h : p.BasicConditions)
    (cert : p.SeparationCertificate) {L E : ℝ} (hL : cert.L₀ ≤ L) (hE : 0 < E)
    (E₀ : ℝ) {z w : Plane}
    (hzw : (z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspPlus) ∨
      (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspMinus)) :
    p.activeReferenceAction L E E₀ + 48 * p.hopMargin ≤
      2 * bridgeAction p.b E₀ p.R + bridgeAction p.b E ‖z + w - 2 • displacement L‖ := by
  have hRL := cert.radius_lt hL
  have hh := same_cusp_action_gap h (show p.R ≤ 2 * L by linarith [h.radius_pos]) hE hzw
  dsimp [activeReferenceAction]
  linarith

/-- The full bridge lies in a fixed positive radial annulus when both source
points lie in the fixed support ball. -/
theorem bridge_distance_annulus {a L : ℝ} (hL : 0 ≤ L) {z w : Plane}
    (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ a) :
    2 * (L - a) ≤ ‖z + w - 2 • displacement L‖ ∧
      ‖z + w - 2 • displacement L‖ ≤ 2 * (L + a) := by
  have hd : ‖2 • displacement L‖ = 2 * L := by
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp [displacement, coordinateVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
  have hsum : ‖z + w‖ ≤ 2 * a := (norm_add_le z w).trans (by linarith)
  have hlo := norm_sub_norm_le (2 • displacement L) (z + w)
  rw [norm_sub_rev, hd] at hlo
  have hup := norm_sub_le (z + w) (2 • displacement L)
  rw [hd] at hup
  constructor <;> linarith

theorem SeparationCertificate.support_annulus {p : CuspParameters} (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) {z w : Plane}
    (hz : z ∈ tsupport p.potential) (hw : w ∈ tsupport p.potential) :
    0 < 2 * (L - cert.supportRadius) ∧
      2 * (L - cert.supportRadius) ≤ ‖z + w - 2 • displacement L‖ ∧
        ‖z + w - 2 • displacement L‖ ≤ 2 * (L + cert.supportRadius) := by
  have haL : cert.supportRadius < L :=
    (lt_of_le_of_lt (le_max_left cert.supportRadius p.R) cert.separation).trans_le hL
  refine ⟨by linarith, ?_⟩
  exact bridge_distance_annulus (cert.supportRadius_pos.le.trans haL.le)
    (cert.support_bound z hz) (cert.support_bound w hw)

theorem potential_eq_zero_iff_components {p : CuspParameters} (h : p.BasicConditions) (x : Plane) :
    p.potential x = 0 ↔ p.core x = 0 ∧ p.cuspPlus x = 0 ∧ p.cuspMinus x = 0 := by
  constructor
  · intro hp
    have hc := (core_range p x).2
    have hp₀ := mul_nonpos_of_nonneg_of_nonpos h.ε_pos.le (cuspPlus_range h x).2
    have hm₀ := mul_nonpos_of_nonneg_of_nonpos h.ε_pos.le (cuspMinus_range h x).2
    dsimp [potential] at hp
    rw [mul_add] at hp
    have hec : p.core x = 0 := by linarith only [hc, hp₀, hm₀, hp]
    have hep : p.ε * p.cuspPlus x = 0 := by linarith only [hc, hp₀, hm₀, hp]
    have hem : p.ε * p.cuspMinus x = 0 := by linarith only [hc, hp₀, hm₀, hp]
    exact ⟨hec, (mul_eq_zero.mp hep).resolve_left h.ε_pos.ne',
      (mul_eq_zero.mp hem).resolve_left h.ε_pos.ne'⟩
  · rintro ⟨hc, hp, hm⟩
    simp [potential, hc, hp, hm]

/-- Cancellation cannot remove a component support: every component is
nonpositive and the cusp coefficient is strictly positive. -/
theorem component_tsupports_subset_potential {p : CuspParameters} (h : p.BasicConditions) :
    tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus ⊆ tsupport p.potential := by
  have hc : tsupport p.core ⊆ tsupport p.potential :=
    closure_mono fun x hx hp => hx ((potential_eq_zero_iff_components h x).mp hp).1
  have hp : tsupport p.cuspPlus ⊆ tsupport p.potential :=
    closure_mono fun x hx hp => hx ((potential_eq_zero_iff_components h x).mp hp).2.1
  have hm : tsupport p.cuspMinus ⊆ tsupport p.potential :=
    closure_mono fun x hx hp => hx ((potential_eq_zero_iff_components h x).mp hp).2.2
  exact union_subset (union_subset hc hp) hm

theorem SeparationCertificate.component_support_annulus {p : CuspParameters}
    (cert : p.SeparationCertificate) (h : p.BasicConditions) {L : ℝ} (hL : cert.L₀ ≤ L)
    {z w : Plane}
    (hz : z ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus)
    (hw : w ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus) :
    0 < 2 * (L - cert.supportRadius) ∧
      2 * (L - cert.supportRadius) ≤ ‖z + w - 2 • displacement L‖ ∧
        ‖z + w - 2 • displacement L‖ ≤ 2 * (L + cert.supportRadius) :=
  cert.support_annulus hL (component_tsupports_subset_potential h hz)
    (component_tsupports_subset_potential h hw)

end InfiniteZero.CuspParameters
