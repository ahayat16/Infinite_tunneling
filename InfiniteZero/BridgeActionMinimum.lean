import InfiniteZero.BridgeAction

/-!
# The proper-time minimum defining the real bridge action

The proper-time phase has a unique minimum at `bridgeTime`, and its value is
the explicit `bridgeAction`. These are the real-variable minimization statements
of P2.2; no assertion about a resolvent kernel is needed here.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

def properTimePhase (b E r τ : ℝ) : ℝ :=
  E * τ + (b * r ^ 2 / 4) * (Real.cosh (b * τ) / Real.sinh (b * τ))

theorem hasDerivAt_properTimePhase {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    (E r : ℝ) : HasDerivAt (properTimePhase b E r)
      (E - b ^ 2 * r ^ 2 / (4 * Real.sinh (b * τ) ^ 2)) τ := by
  have hs : 0 < Real.sinh (b * τ) := Real.sinh_pos_iff.2 (mul_pos hb hτ)
  have hbτ := (hasDerivAt_id τ).const_mul b
  have hquot := hbτ.cosh.div hbτ.sinh hs.ne'
  have hd := ((hasDerivAt_id τ).const_mul E).add (hquot.const_mul (b * r ^ 2 / 4))
  convert hd using 1
  simp only [id, mul_one]
  have hyp := Real.cosh_sq_sub_sinh_sq (b * τ)
  field_simp
  nlinarith [congrArg (fun x : ℝ => b ^ 2 * r ^ 2 * x) hyp]

theorem deriv_properTimePhase {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) (E r : ℝ) :
    deriv (properTimePhase b E r) τ =
      E - b ^ 2 * r ^ 2 / (4 * Real.sinh (b * τ) ^ 2) :=
  (hasDerivAt_properTimePhase hb hτ E r).deriv

theorem hasDerivAt_deriv_properTimePhase {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    (E r : ℝ) : HasDerivAt (deriv (properTimePhase b E r))
      (b ^ 3 * r ^ 2 * Real.cosh (b * τ) / (2 * Real.sinh (b * τ) ^ 3)) τ := by
  have hs : 0 < Real.sinh (b * τ) := Real.sinh_pos_iff.2 (mul_pos hb hτ)
  have hden := (((hasDerivAt_id τ).const_mul b).sinh.pow 2).const_mul 4
  have hd := (((hasDerivAt_const τ (b ^ 2 * r ^ 2)).div hden (by
    simp only [id, Pi.pow_apply]
    positivity))).const_sub E
  have hd' : HasDerivAt (fun x => E - b ^ 2 * r ^ 2 / (4 * Real.sinh (b * x) ^ 2))
      (b ^ 3 * r ^ 2 * Real.cosh (b * τ) / (2 * Real.sinh (b * τ) ^ 3)) τ := by
    convert hd using 1
    simp only [id, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hτ] with x hx
  exact deriv_properTimePhase hb hx E r

theorem deriv2_properTimePhase {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) (E r : ℝ) :
    deriv (deriv (properTimePhase b E r)) τ =
      b ^ 3 * r ^ 2 * Real.cosh (b * τ) / (2 * Real.sinh (b * τ) ^ 3) :=
  (hasDerivAt_deriv_properTimePhase hb hτ E r).deriv

theorem deriv2_properTimePhase_pos {b r τ : ℝ}
    (hb : 0 < b) (hr : 0 < r) (hτ : 0 < τ) (E : ℝ) :
    0 < deriv (deriv (properTimePhase b E r)) τ := by
  rw [deriv2_properTimePhase hb hτ]
  have hs : 0 < Real.sinh (b * τ) := Real.sinh_pos_iff.2 (mul_pos hb hτ)
  have hc := Real.cosh_pos (b * τ)
  positivity

theorem strictConvexOn_properTimePhase {b r : ℝ} (hb : 0 < b) (hr : 0 < r) (E : ℝ) :
    StrictConvexOn ℝ (Ioi 0) (properTimePhase b E r) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
    (fun τ hτ => (hasDerivAt_properTimePhase hb hτ E r).continuousAt.continuousWithinAt)
  intro τ hτ
  exact deriv2_properTimePhase_pos hb hr hτ E

theorem hasDerivAt_properTimePhase_bridgeTime {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    HasDerivAt (properTimePhase b E r) 0 (bridgeTime b E r) := by
  have hd := hasDerivAt_properTimePhase hb (bridgeTime_pos hb hE hr) E r
  rw [sinh_bridgeTime hb.ne'] at hd
  convert hd using 1
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hsq := Real.sq_sqrt hE.le
  field_simp
  nlinarith

theorem deriv_properTimePhase_eq_zero_iff {b E r τ : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hτ : 0 < τ) :
    deriv (properTimePhase b E r) τ = 0 ↔ τ = bridgeTime b E r := by
  have hstar := (hasDerivAt_properTimePhase_bridgeTime hb hE hr).deriv
  constructor
  · intro hzero
    have hm : StrictMonoOn (deriv (properTimePhase b E r)) (Ioi 0) :=
      (strictConvexOn_properTimePhase hb hr E).strictMonoOn_deriv
      (fun t ht => (hasDerivAt_properTimePhase hb ht E r).differentiableAt)
    exact hm.injOn hτ (bridgeTime_pos hb hE hr) (hzero.trans hstar.symm)
  · rintro rfl
    exact hstar

theorem isMinOn_properTimePhase_bridgeTime {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    IsMinOn (properTimePhase b E r) (Ioi 0) (bridgeTime b E r) := by
  apply (strictConvexOn_properTimePhase hb hr E).convexOn.isMinOn_of_rightDeriv_eq_zero
  · simpa only [interior_Ioi, mem_Ioi] using bridgeTime_pos hb hE hr
  · exact (hasDerivAt_properTimePhase_bridgeTime hb hE hr).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi _)

theorem isMinOn_properTimePhase_iff {b E r τ : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hτ : 0 < τ) :
    IsMinOn (properTimePhase b E r) (Ioi 0) τ ↔ τ = bridgeTime b E r := by
  constructor
  · intro hm
    exact (strictConvexOn_properTimePhase hb hr E).eq_of_isMinOn hm
      (isMinOn_properTimePhase_bridgeTime hb hE hr) hτ (bridgeTime_pos hb hE hr)
  · rintro rfl
    exact isMinOn_properTimePhase_bridgeTime hb hE hr

/-- Evaluation of the phase at its unique critical point gives the explicit action. -/
theorem properTimePhase_bridgeTime {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    properTimePhase b E r (bridgeTime b E r) = bridgeAction b E r := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hs2 := Real.sq_sqrt hE.le
  have hA : 0 < b ^ 2 * r ^ 2 + 4 * E := by positivity
  have hA2 := Real.sq_sqrt hA.le
  have hroot : Real.sqrt (1 + (b * r / (2 * Real.sqrt E)) ^ 2) =
      Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) / (2 * Real.sqrt E) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    field_simp
    nlinarith
  simp only [properTimePhase, bridgeTime, bridgeAction, mul_div_cancel₀ _ hb.ne',
    Real.cosh_arsinh, Real.sinh_arsinh, hroot]
  field_simp
  ring

theorem bridgeAction_le_properTimePhase {b E r τ : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hτ : 0 < τ) :
    bridgeAction b E r ≤ properTimePhase b E r τ := by
  rw [← properTimePhase_bridgeTime hb hE hr]
  exact isMinOn_properTimePhase_bridgeTime hb hE hr hτ

theorem properTimePhase_eq_bridgeAction_iff {b E r τ : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hτ : 0 < τ) :
    properTimePhase b E r τ = bridgeAction b E r ↔ τ = bridgeTime b E r := by
  constructor
  · intro heq
    apply (isMinOn_properTimePhase_iff hb hE hr hτ).1
    intro t ht
    rw [heq]
    exact bridgeAction_le_properTimePhase hb hE hr ht
  · rintro rfl
    exact properTimePhase_bridgeTime hb hE hr

theorem existsUnique_properTimePhase_minimizer {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    ∃! τ, 0 < τ ∧ IsMinOn (properTimePhase b E r) (Ioi 0) τ := by
  refine ⟨bridgeTime b E r, ⟨bridgeTime_pos hb hE hr,
    isMinOn_properTimePhase_bridgeTime hb hE hr⟩, ?_⟩
  intro τ hτ
  exact (isMinOn_properTimePhase_iff hb hE hr hτ.1).1 hτ.2

theorem bridgeAction_isLeast_properTimePhase {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    IsLeast (properTimePhase b E r '' Ioi 0) (bridgeAction b E r) := by
  constructor
  · exact ⟨bridgeTime b E r, bridgeTime_pos hb hE hr, properTimePhase_bridgeTime hb hE hr⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    exact bridgeAction_le_properTimePhase hb hE hr hτ

/-- The infimum representation from the definition of the bridge action in P2.2. -/
theorem bridgeAction_eq_sInf_properTimePhase {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    bridgeAction b E r = sInf (properTimePhase b E r '' Ioi 0) :=
  (bridgeAction_isLeast_properTimePhase hb hE hr).csInf_eq.symm

end InfiniteZero
