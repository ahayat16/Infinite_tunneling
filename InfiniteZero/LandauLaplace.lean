import InfiniteZero.LandauKernelUniform

/-!
# Quantitative localization of the proper-time minimum

These estimates establish the uniform positive Hessian and off-graph phase gap
needed for Laplace's method. The leading Gaussian asymptotic is not assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

/-- A lower bound for the proper-time Hessian on `0 < τ ≤ U`, `r ≥ rmin`. -/
def properTimeHessianFloor (b rmin U : ℝ) : ℝ :=
  b ^ 3 * rmin ^ 2 / (2 * Real.sinh (b * U) ^ 3)

theorem properTimeHessianFloor_pos {b rmin U : ℝ}
    (hb : 0 < b) (hrmin : 0 < rmin) (hU : 0 < U) :
    0 < properTimeHessianFloor b rmin U := by
  unfold properTimeHessianFloor
  have hs : 0 < Real.sinh (b * U) := Real.sinh_pos_iff.2 (mul_pos hb hU)
  positivity

theorem properTimeHessianFloor_le {b rmin r U τ : ℝ}
    (hb : 0 < b) (hrmin : 0 < rmin) (hr : rmin ≤ r)
    (hτ : 0 < τ) (hτU : τ ≤ U) (E : ℝ) :
    properTimeHessianFloor b rmin U ≤ deriv (deriv (properTimePhase b E r)) τ := by
  unfold properTimeHessianFloor
  rw [deriv2_properTimePhase hb hτ]
  have hrp : 0 < r := hrmin.trans_le hr
  have hs : 0 < Real.sinh (b * τ) := Real.sinh_pos_iff.2 (mul_pos hb hτ)
  have hcosh := Real.one_le_cosh (b * τ)
  refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
  · calc
      b ^ 3 * rmin ^ 2 ≤ b ^ 3 * r ^ 2 := by gcongr
      _ ≤ b ^ 3 * r ^ 2 * Real.cosh (b * τ) := by nlinarith [mul_nonneg (by positivity : 0 ≤ b ^ 3 * r ^ 2) (sub_nonneg.mpr hcosh)]
  · have hsin : Real.sinh (b * τ) ≤ Real.sinh (b * U) :=
      Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_left hτU hb.le)
    gcongr

theorem bridgeTime_mem_uniform_Icc {b Emin Emax rmin rmax E r : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hrmin : 0 < rmin)
    (hE : E ∈ Icc Emin Emax) (hr : r ∈ Icc rmin rmax) :
    bridgeTime b E r ∈ Icc (bridgeTime b Emax rmin) (bridgeTime b Emin rmax) := by
  have hEp := hEmin.trans_le hE.1
  have hrp := hrmin.trans_le hr.1
  exact ⟨bridgeTime_le_of_energy_radius_bounds hb hEp hrp hE.2 hr.1,
    bridgeTime_le_of_energy_radius_bounds hb hEmin (hrp.trans_le hr.2) hE.1 hr.2⟩

/-- Uniform nondegeneracy on any fixed positive-time neighborhood of the critical graph. -/
theorem exists_uniform_properTimePhase_hessian_lower {b Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) (hε : 0 < ε) :
    ∃ m > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rmin rmax, ∀ τ > 0,
      |τ - bridgeTime b E r| ≤ ε → m ≤ deriv (deriv (properTimePhase b E r)) τ := by
  let T := bridgeTime b Emin rmax
  have hT : 0 < T := bridgeTime_pos hb hEmin (hrmin.trans_le hrmax)
  refine ⟨properTimeHessianFloor b rmin (T + ε),
    properTimeHessianFloor_pos hb hrmin (by positivity), ?_⟩
  intro E hE r hr τ hτ hdist
  apply properTimeHessianFloor_le hb hrmin hr.1 hτ _ E
  have haT := (bridgeTime_mem_uniform_Icc hb hEmin hrmin hE hr).2
  have hupper := (abs_le.mp hdist).2
  dsimp [T]
  linarith

/-- A Hessian lower bound gives an exact quadratic lower bound around the minimum. -/
theorem properTimePhase_ge_quadratic {b E r U m τ : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r)
    (hstarU : bridgeTime b E r < U)
    (hH : ∀ t ∈ Ioc 0 U, m ≤ deriv (deriv (properTimePhase b E r)) t)
    (hτ : 0 < τ) (hτU : τ ≤ U) :
    bridgeAction b E r + m / 2 * (τ - bridgeTime b E r) ^ 2 ≤ properTimePhase b E r τ := by
  let a := bridgeTime b E r
  let f := fun t => properTimePhase b E r t - m / 2 * (t - a) ^ 2
  let f' := fun t => deriv (properTimePhase b E r) t - m * (t - a)
  have ha : 0 < a := bridgeTime_pos hb hE hr
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt f (f' t) t := by
    have hp := (((hasDerivAt_id t).sub_const a).pow 2).const_mul (m / 2)
    convert (hasDerivAt_properTimePhase hb ht E r).differentiableAt.hasDerivAt.sub hp using 1
    simp only [f', id, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  have hdd (t : ℝ) (ht : 0 < t) : HasDerivAt f'
      (deriv (deriv (properTimePhase b E r)) t - m) t := by
    convert (hasDerivAt_deriv_properTimePhase hb ht E r).differentiableAt.hasDerivAt.sub
      (((hasDerivAt_id t).sub_const a).const_mul m) using 1
    simp only [mul_one]
  have hconv : ConvexOn ℝ (Ioc 0 U) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 U)
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht).1).hasDerivWithinAt)
      (fun t ht => (hdd t (interior_subset ht).1).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hH t (interior_subset ht))
  have hmin : IsMinOn f (Ioc 0 U) a := by
    apply hconv.isMinOn_of_rightDeriv_eq_zero
    · simpa only [interior_Ioc, mem_Ioo] using (show 0 < a ∧ a < U from ⟨ha, hstarU⟩)
    · have hda : HasDerivAt f 0 a := by
        convert hd a ha using 1
        dsimp [f', a]
        rw [(hasDerivAt_properTimePhase_bridgeTime hb hE hr).deriv]
        ring
      exact hda.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi _)
  have hbound := hmin (show τ ∈ Ioc 0 U from ⟨hτ, hτU⟩)
  dsimp [f, a] at hbound
  rw [properTimePhase_bridgeTime hb hE hr] at hbound
  nlinarith

theorem monotoneOn_properTimePhase_right {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    MonotoneOn (properTimePhase b E r) (Ici (bridgeTime b E r)) := by
  have ha := bridgeTime_pos hb hE hr
  have hdm : MonotoneOn (deriv (properTimePhase b E r)) (Ioi 0) :=
    (strictConvexOn_properTimePhase hb hr E).convexOn.monotoneOn_deriv
      (fun t ht => (hasDerivAt_properTimePhase hb ht E r).differentiableAt)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (fun t ht => (hasDerivAt_properTimePhase hb (ha.trans_le ht) E r).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_properTimePhase hb (ha.trans_le (interior_subset ht)) E r).differentiableAt.differentiableWithinAt)
  intro t ht
  have h := hdm ha (ha.trans_le (interior_subset ht)) (interior_subset ht)
  rwa [(hasDerivAt_properTimePhase_bridgeTime hb hE hr).deriv] at h

/-- A uniform off-graph gap on the full positive time axis, not only a compact strip. -/
theorem exists_uniform_properTimePhase_gap {b Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) (hε : 0 < ε) :
    ∃ q > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rmin rmax, ∀ τ > 0,
      ε ≤ |τ - bridgeTime b E r| → bridgeAction b E r + q ≤ properTimePhase b E r τ := by
  let T := bridgeTime b Emin rmax
  have hT : 0 < T := bridgeTime_pos hb hEmin (hrmin.trans_le hrmax)
  let m := properTimeHessianFloor b rmin (T + ε)
  have hm : 0 < m := properTimeHessianFloor_pos hb hrmin (by positivity)
  refine ⟨m / 2 * ε ^ 2, by positivity, ?_⟩
  intro E hE r hr τ hτ hdist
  have hEp : 0 < E := hEmin.trans_le hE.1
  have hrp : 0 < r := hrmin.trans_le hr.1
  let a := bridgeTime b E r
  have ha : 0 < a := bridgeTime_pos hb hEp hrp
  have haT : a ≤ T := (bridgeTime_mem_uniform_Icc hb hEmin hrmin hE hr).2
  have haU : a < T + ε := by linarith
  have hH : ∀ t ∈ Ioc 0 (T + ε), m ≤ deriv (deriv (properTimePhase b E r)) t :=
    fun t ht => properTimeHessianFloor_le hb hrmin hr.1 ht.1 ht.2 E
  by_cases htU : τ ≤ T + ε
  · have hquad := properTimePhase_ge_quadratic hb hEp hrp haU hH hτ htU
    have hsq : ε ^ 2 ≤ (τ - a) ^ 2 := by
      have h := sq_le_sq₀ hε.le (abs_nonneg (τ - a)) |>.2 hdist
      simpa only [sq_abs] using h
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ m / 2 by positivity)
    dsimp [a] at hmul
    linarith
  · have hquad := properTimePhase_ge_quadratic hb hEp hrp haU hH
      (show 0 < a + ε by positivity) (show a + ε ≤ T + ε by linarith)
    have hmono := monotoneOn_properTimePhase_right hb hEp hrp
      (show bridgeTime b E r ≤ a + ε by dsimp [a]; linarith)
      (show bridgeTime b E r ≤ τ by dsimp [a] at *; linarith)
      (show a + ε ≤ τ by linarith)
    dsimp [a] at hquad
    ring_nf at hquad
    linarith

end InfiniteZero
