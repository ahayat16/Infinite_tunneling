import InfiniteZero.ConstructionCoreSmooth
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The unchanged unique minimum of the fixed potential

The exterior cusps vanish throughout the radial core ball.  Their total
depth outside that ball is strictly less than one.  Consequently the
constructed potential has the same unique global minimum as the core,
and its germ at zero is exactly the smooth radial-core germ.
-/

noncomputable section

open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

theorem potential_eq_core_of_norm_le {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : ‖x‖ ≤ p.r₀) : p.potential x = p.core x := by
  simp [potential, cuspPlus_eq_zero_of_norm_le h hx, cuspMinus_eq_zero_of_norm_le h hx]

theorem potential_zero {p : CuspParameters} (h : p.BasicConditions) :
    p.potential 0 = -1 := by
  rw [potential_eq_core_of_norm_le h (by simpa using h.r₀_pos.le), core_zero h.r₀_pos]

/-- The exterior components cannot create another global minimum. -/
theorem potential_gt_neg_one {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ≠ 0) : -1 < p.potential x := by
  rcases core_cusp_separation h x with hcore | ⟨hplus, hminus⟩
  · have hp := (cuspPlus_range h x).1
    have hm := (cuspMinus_range h x).1
    have hsum : -2 * p.a ≤ p.cuspPlus x + p.cuspMinus x := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hsum h.ε_pos.le
    unfold potential
    rw [hcore]
    nlinarith [h.depth_small]
  · simpa [potential, hplus, hminus] using core_gt_neg_one hx

theorem potential_unique_minimum {p : CuspParameters} (h : p.BasicConditions) :
    p.potential 0 = -1 ∧ ∀ x : Plane, x ≠ 0 → p.potential 0 < p.potential x := by
  refine ⟨potential_zero h, ?_⟩
  intro x hx
  rw [potential_zero h]
  exact potential_gt_neg_one h hx

/-- The perturbation vanishes on an actual open neighborhood of the minimum. -/
theorem potential_eventuallyEq_core {p : CuspParameters} (h : p.BasicConditions) :
    p.potential =ᶠ[𝓝 (0 : Plane)] p.core := by
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) h.r₀_pos] with x hx
  apply potential_eq_core_of_norm_le h
  have hn : ‖x‖ < p.r₀ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  exact hn.le

theorem potential_isLocalMin_zero {p : CuspParameters} (h : p.BasicConditions) :
    IsLocalMin p.potential (0 : Plane) := by
  apply Filter.Eventually.of_forall
  intro x
  rw [potential_zero h]
  exact (potential_range h x).1

theorem potential_contDiffAt_zero {p : CuspParameters} (h : p.BasicConditions) :
    ContDiffAt ℝ ∞ p.potential (0 : Plane) :=
  (core_contDiff h.r₀_pos).contDiffAt.congr_of_eventuallyEq (potential_eventuallyEq_core h)

/-- The potential is differentiable at its minimum even before proving the
flat extension at either distant cusp tip. -/
theorem potential_differentiableAt_zero {p : CuspParameters} (h : p.BasicConditions) :
    DifferentiableAt ℝ p.potential (0 : Plane) := by
  apply (potential_eventuallyEq_core h).differentiableAt_iff.mpr
  exact ((core_contDiff h.r₀_pos).differentiable (by simp)).differentiableAt

theorem potential_fderiv_zero {p : CuspParameters} (h : p.BasicConditions) :
    fderiv ℝ p.potential (0 : Plane) = 0 :=
  (potential_isLocalMin_zero h).fderiv_eq_zero

/-- This derivative statement includes differentiability, rather than merely
the default-zero value of `fderiv` for a nondifferentiable function. -/
theorem potential_hasFDerivAt_zero {p : CuspParameters} (h : p.BasicConditions) :
    HasFDerivAt p.potential (0 : Plane →L[ℝ] ℝ) (0 : Plane) := by
  simpa only [potential_fderiv_zero h] using (potential_differentiableAt_zero h).hasFDerivAt

/-- The scalar profile in the squared radial coordinate, near zero. -/
def radialCoreProfile (p : CuspParameters) (q : ℝ) : ℝ :=
  -Real.exp (-(q / (p.r₀ ^ 2 - q)))

theorem radialCoreProfile_contDiffAt_zero {p : CuspParameters} (hr : 0 < p.r₀) :
    ContDiffAt ℝ 2 p.radialCoreProfile (0 : ℝ) := by
  have hd : p.r₀ ^ 2 - (0 : ℝ) ≠ 0 := by
    simpa only [sub_zero] using (sq_pos_of_pos hr).ne'
  exact ((contDiffAt_id.div (contDiffAt_const.sub contDiffAt_id) hd).neg.exp).neg

theorem radialCoreProfile_hasDerivAt_zero {p : CuspParameters} (hr : 0 < p.r₀) :
    HasDerivAt p.radialCoreProfile (1 / p.r₀ ^ 2) (0 : ℝ) := by
  have hd : p.r₀ ^ 2 - (0 : ℝ) ≠ 0 := by
    simpa only [sub_zero] using (sq_pos_of_pos hr).ne'
  have hh := (((hasDerivAt_id (0 : ℝ)).div
    ((hasDerivAt_const (0 : ℝ) (p.r₀ ^ 2)).sub (hasDerivAt_id (0 : ℝ))) hd).neg.exp).neg
  convert hh using 1
  simp
  field_simp [hr.ne']

theorem potential_eventuallyEq_radialCoreProfile {p : CuspParameters} (h : p.BasicConditions) :
    p.potential =ᶠ[𝓝 (0 : Plane)] (fun x => p.radialCoreProfile (‖x‖ ^ 2)) := by
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) h.r₀_pos] with x hx
  have hn : ‖x‖ < p.r₀ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  rw [potential_eq_core_of_norm_le h hn.le]
  simp only [core, if_pos hn, radialCoreProfile]

/-- The second derivative along any line through the minimum has the exact
positive quadratic coefficient stated in the manuscript. -/
theorem potential_second_directional_derivative {p : CuspParameters}
    (h : p.BasicConditions) (u : Plane) :
    iteratedDeriv 2 (fun t : ℝ => p.potential (t • u)) 0 =
      2 * ‖u‖ ^ 2 / p.r₀ ^ 2 := by
  let q : ℝ → ℝ := fun t => t ^ 2 * ‖u‖ ^ 2
  have hline : Filter.Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 (0 : Plane)) := by
    have hcont : Continuous (fun t : ℝ => t • u) := continuous_id.smul continuous_const
    simpa using hcont.tendsto (0 : ℝ)
  have heq : (fun t : ℝ => p.potential (t • u)) =ᶠ[𝓝 0] p.radialCoreProfile ∘ q := by
    have he := (potential_eventuallyEq_radialCoreProfile h).comp_tendsto hline
    simpa only [Function.comp_def, q, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using he
  rw [heq.iteratedDeriv_eq 2]
  have hq : ContDiffAt ℝ 2 q 0 := (contDiffAt_id.pow 2).mul contDiffAt_const
  have hg : ContDiffAt ℝ 2 p.radialCoreProfile (q 0) := by
    simpa only [q, zero_pow (by decide : 2 ≠ 0), zero_mul] using
      radialCoreProfile_contDiffAt_zero h.r₀_pos
  have hq1 : deriv q 0 = 0 := by
    simp [q]
  have hq2 : iteratedDeriv 2 q 0 = 2 * ‖u‖ ^ 2 := by
    dsimp only [q]
    rw [iteratedDeriv_mul_const_field]
    norm_num
  rw [iteratedDeriv_comp_two hg hq, hq1, hq2]
  simp only [q, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, zero_add]
  rw [(radialCoreProfile_hasDerivAt_zero h.r₀_pos).deriv]
  ring

theorem potential_second_directional_derivative_pos {p : CuspParameters}
    (h : p.BasicConditions) {u : Plane} (hu : u ≠ 0) :
    0 < iteratedDeriv 2 (fun t : ℝ => p.potential (t • u)) 0 := by
  rw [potential_second_directional_derivative h]
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hu)))
    (sq_pos_of_pos h.r₀_pos)

end InfiniteZero.CuspParameters
