import InfiniteZero.GeometryAction
import Mathlib.Data.Complex.Basic

/-!
# Exact outgoing action derivatives at the cross pair

This proves P2.6's normal derivatives of the radial incoming action and the
bridge action in both variables. Their sum is positive, so the complex saddle
coefficient has positive real part.
-/

noncomputable section

namespace InfiniteZero.Geometry

theorem sqNorm_normalLine (p n : Point) (t : ℝ) :
    sqNorm (normalLine p n t) = sqNorm p + 2 * t * dot p n + t ^ 2 * sqNorm n := by
  dsimp [sqNorm, normalLine, dot]
  ring

@[simp] theorem normalLine_zero (p n : Point) : normalLine p n 0 = p := by
  ext <;> simp [normalLine]

theorem bridge_normalLine_left (L : ℝ) (z w n : Point) (t : ℝ) :
    bridge L (normalLine z n t) w = normalLine (bridge L z w) n t := by
  ext <;> dsimp [bridge, normalLine] <;> ring

theorem bridge_normalLine_right (L : ℝ) (z w n : Point) (t : ℝ) :
    bridge L z (normalLine w n t) = normalLine (bridge L z w) n t := by
  ext <;> dsimp [bridge, normalLine] <;> ring

/-- Both the radial and bridge lengths have first derivative `1/2` because
the unit outgoing vector has radial projection `1/2`. -/
theorem hasDerivAt_length_normalLine {r : ℝ} (hr : 0 < r) {p n : Point}
    (hp : sqNorm p = r ^ 2) (hd : dot p n = r / 2) (hn : sqNorm n = 1) :
    HasDerivAt (fun t => length (normalLine p n t)) (1 / 2 : ℝ) 0 := by
  have heq : (fun t => length (normalLine p n t)) =
      (fun t => Real.sqrt (r ^ 2 + r * t + t ^ 2)) := by
    funext t
    rw [length, sqNorm_normalLine, hp, hd, hn]
    congr 1
    ring
  rw [heq]
  have hq : HasDerivAt (fun t : ℝ => r ^ 2 + r * t + t ^ 2) r 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul r).const_add (r ^ 2)).add
      ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
    norm_num
  have hs := hq.sqrt (by simpa using pow_ne_zero 2 hr.ne')
  convert hs using 1
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), Real.sqrt_sq hr.le]
  field_simp

theorem hasDerivAt_radial_action_normalLine {b E r : ℝ} (hb : b ≠ 0) (hE : 0 < E)
    (hr : 0 < r) {p n : Point} (hp : sqNorm p = r ^ 2) (hd : dot p n = r / 2)
    (hn : sqNorm n = 1) :
    HasDerivAt (fun t => bridgeAction b E (length (normalLine p n t)))
      (deriv (bridgeAction b E) r / 2) 0 := by
  have hlen := hasDerivAt_length_normalLine hr hp hd hn
  have h0 : r = length (normalLine p n 0) := by
    rw [normalLine_zero, length, hp, Real.sqrt_sq hr.le]
  have hj := ((differentiable_bridgeAction hb hE r).hasDerivAt).comp_of_eq 0 hlen h0
  simpa only [Function.comp_def, div_eq_mul_inv, one_div, one_mul] using hj

theorem hasDerivAt_radial_action_tipPlus {b E R : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hR : 0 < R) :
    HasDerivAt (fun t => bridgeAction b E (length (normalLine (tipPlus R) normalPlus t)))
      (deriv (bridgeAction b E) R / 2) 0 :=
  hasDerivAt_radial_action_normalLine hb hE hR (sqNorm_tipPlus R)
    (tipPlus_dot_normalPlus R) normalPlus_unit

theorem hasDerivAt_radial_action_tipMinus {b E R : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hR : 0 < R) :
    HasDerivAt (fun t => bridgeAction b E (length (normalLine (tipMinus R) normalMinus t)))
      (deriv (bridgeAction b E) R / 2) 0 :=
  hasDerivAt_radial_action_normalLine hb hE hR (sqNorm_tipMinus R)
    (tipMinus_dot_normalMinus R) normalMinus_unit

theorem dot_bridge_normalPlus (R L : ℝ) :
    dot (bridge L (tipPlus R) (tipMinus R)) normalPlus = activeDistance R L / 2 := by
  rw [bridge_cross]
  dsimp [dot, normalPlus]
  ring

theorem dot_bridge_normalMinus (R L : ℝ) :
    dot (bridge L (tipPlus R) (tipMinus R)) normalMinus = activeDistance R L / 2 := by
  rw [bridge_cross]
  dsimp [dot, normalMinus]
  ring

theorem hasDerivAt_bridge_action_normal_plus {b E R L : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hL : R < 2 * L) :
    HasDerivAt (fun t => bridgeAction b E
      (length (bridge L (normalLine (tipPlus R) normalPlus t) (tipMinus R))))
      (deriv (bridgeAction b E) (activeDistance R L) / 2) 0 := by
  simp_rw [bridge_normalLine_left]
  exact hasDerivAt_radial_action_normalLine hb hE (activeDistance_pos hL)
    (sqNorm_bridge_cross R L) (dot_bridge_normalPlus R L) normalPlus_unit

theorem hasDerivAt_bridge_action_normal_minus {b E R L : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hL : R < 2 * L) :
    HasDerivAt (fun t => bridgeAction b E
      (length (bridge L (tipPlus R) (normalLine (tipMinus R) normalMinus t))))
      (deriv (bridgeAction b E) (activeDistance R L) / 2) 0 := by
  simp_rw [bridge_normalLine_right]
  exact hasDerivAt_radial_action_normalLine hb hE (activeDistance_pos hL)
    (sqNorm_bridge_cross R L) (dot_bridge_normalMinus R L) normalMinus_unit

/-- The common outgoing slope of the full real action at the active cross pair. -/
def activeActionSlope (b E R L : ℝ) : ℝ :=
  (deriv (bridgeAction b E) R + deriv (bridgeAction b E) (activeDistance R L)) / 2

def realPairAction (b E L : ℝ) (z w : Point) : ℝ :=
  bridgeAction b E (length z) + bridgeAction b E (length w) +
    bridgeAction b E (length (bridge L z w))

theorem hasDerivAt_realPairAction_normal_plus {b E R L : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hR : 0 < R) (hL : R < 2 * L) :
    HasDerivAt (fun t => realPairAction b E L (normalLine (tipPlus R) normalPlus t) (tipMinus R))
      (activeActionSlope b E R L) 0 := by
  convert ((hasDerivAt_radial_action_tipPlus hb hE hR).add_const
    (bridgeAction b E (length (tipMinus R)))).add
      (hasDerivAt_bridge_action_normal_plus hb hE hL) using 1
  dsimp [activeActionSlope]
  ring

theorem hasDerivAt_realPairAction_normal_minus {b E R L : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hR : 0 < R) (hL : R < 2 * L) :
    HasDerivAt (fun t => realPairAction b E L (tipPlus R) (normalLine (tipMinus R) normalMinus t))
      (activeActionSlope b E R L) 0 := by
  convert ((hasDerivAt_radial_action_tipMinus hb hE hR).const_add
    (bridgeAction b E (length (tipPlus R)))).add
      (hasDerivAt_bridge_action_normal_minus hb hE hL) using 1
  dsimp [activeActionSlope]
  ring

theorem activeActionSlope_pos {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (R L : ℝ) :
    0 < activeActionSlope b E R L := by
  exact div_pos (add_pos (deriv_bridgeAction_pos hb hE R)
    (deriv_bridgeAction_pos hb hE (activeDistance R L))) (by norm_num)

/-- The complex normal saddle coefficient lies in the open right half-plane. -/
theorem active_complex_slope_re_pos {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (R L : ℝ) :
    0 < ((activeActionSlope b E R L : ℂ) - Complex.I * (phaseSlope b L : ℂ)).re := by
  simpa using activeActionSlope_pos hb hE R L

end InfiniteZero.Geometry
