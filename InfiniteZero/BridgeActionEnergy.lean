import InfiniteZero.BridgeAction

/-!
# Energy dependence of the real bridge action

These identities are proved directly from the explicit real formula.  They
do not use the identification of the action as a minimized proper-time phase.
-/

noncomputable section

open Set

namespace InfiniteZero

private theorem energy_radicand_pos (b r : ℝ) {E : ℝ} (hE : 0 < E) :
    0 < b ^ 2 * r ^ 2 + 4 * E := by positivity

private theorem energy_sqrt_rescale (b r : ℝ) {E : ℝ} (hE : 0 < E) :
    Real.sqrt (1 + (b * r / (2 * Real.sqrt E)) ^ 2) =
      Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) / (2 * Real.sqrt E) := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hs2 := Real.sq_sqrt hE.le
  have hA := Real.sq_sqrt (energy_radicand_pos b r hE).le
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  field_simp
  nlinarith

/-- The energy derivative equals the explicit proper time, for every real
radius (including zero and the odd extension to negative radii). -/
theorem hasDerivAt_bridgeAction_energy {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    HasDerivAt (fun energy => bridgeAction b energy r) (bridgeTime b E r) E := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hA : 0 < Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) :=
    Real.sqrt_pos.2 (energy_radicand_pos b r hE)
  have hrad := ((hasDerivAt_id E).const_mul 4).const_add (b ^ 2 * r ^ 2)
  have hfirst := (hrad.sqrt (ne_of_gt (energy_radicand_pos b r hE))).const_mul (r / 4)
  have hroot := ((hasDerivAt_id E).sqrt hE.ne').const_mul 2
  have hquot := (hasDerivAt_const E (b * r)).div hroot (ne_of_gt (mul_pos (by norm_num) hs))
  have hsecond := ((hasDerivAt_id E).div_const b).mul hquot.arsinh
  convert hfirst.add hsecond using 1
  simp only [id, Pi.div_apply, smul_eq_mul, mul_one, zero_mul, zero_sub]
  rw [energy_sqrt_rescale b r hE]
  unfold bridgeTime
  have hs2 := Real.sq_sqrt hE.le
  field_simp
  rw [hs2]
  ring

theorem deriv_bridgeAction_energy {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    deriv (fun energy => bridgeAction b energy r) E = bridgeTime b E r :=
  (hasDerivAt_bridgeAction_energy hb hE r).deriv

theorem differentiableOn_bridgeAction_energy {b : ℝ} (hb : b ≠ 0) (r : ℝ) :
    DifferentiableOn ℝ (fun E => bridgeAction b E r) (Ioi 0) :=
  fun _ hE => (hasDerivAt_bridgeAction_energy hb hE r).differentiableAt.differentiableWithinAt

theorem continuousOn_bridgeAction_energy {b : ℝ} (hb : b ≠ 0) (r : ℝ) :
    ContinuousOn (fun E => bridgeAction b E r) (Ioi 0) :=
  (differentiableOn_bridgeAction_energy hb r).continuousOn

@[simp] theorem bridgeTime_neg_field (b E r : ℝ) :
    bridgeTime (-b) E r = bridgeTime b E r := by
  simp [bridgeTime, neg_mul, neg_div, div_neg, Real.arsinh_neg]

theorem bridgeTime_pos_of_ne_zero {b E r : ℝ} (hb : b ≠ 0) (hE : 0 < E) (hr : 0 < r) :
    0 < bridgeTime b E r := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · simpa only [bridgeTime_neg_field] using bridgeTime_pos (neg_pos.mpr hbneg) hE hr
  · exact bridgeTime_pos hbpos hE hr

theorem strictMonoOn_bridgeAction_energy {b r : ℝ} (hb : b ≠ 0) (hr : 0 < r) :
    StrictMonoOn (fun E => bridgeAction b E r) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (continuousOn_bridgeAction_energy hb r)
  intro E hE
  have hEpos : 0 < E := interior_subset hE
  rw [deriv_bridgeAction_energy hb hEpos]
  exact bridgeTime_pos_of_ne_zero hb hEpos hr

theorem bridgeAction_energy_lt {b r E₁ E₂ : ℝ} (hb : b ≠ 0) (hr : 0 < r)
    (hE₁ : 0 < E₁) (hE : E₁ < E₂) : bridgeAction b E₁ r < bridgeAction b E₂ r :=
  strictMonoOn_bridgeAction_energy hb hr hE₁ (hE₁.trans hE) hE

theorem monotoneOn_bridgeAction_energy {b r : ℝ} (hb : b ≠ 0) (hr : 0 < r) :
    MonotoneOn (fun E => bridgeAction b E r) (Ioi 0) :=
  (strictMonoOn_bridgeAction_energy hb hr).monotoneOn

theorem bridgeAction_energy_le {b r E₁ E₂ : ℝ} (hb : b ≠ 0) (hr : 0 < r)
    (hE₁ : 0 < E₁) (hE : E₁ ≤ E₂) : bridgeAction b E₁ r ≤ bridgeAction b E₂ r :=
  monotoneOn_bridgeAction_energy hb hr hE₁ (hE₁.trans_le hE) hE

end InfiniteZero
