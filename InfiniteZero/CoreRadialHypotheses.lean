import InfiniteZero.ConstructionMinimum

/-!
# Classical radial hypotheses for the explicit reference core

Only the core radius is assumed positive. No condition on the cusps or the
full potential enters these smoothness, support and nondegeneracy statements.
The radial variable here is the signed radius, unlike `radialCoreProfile`,
whose argument is the squared radius.
-/

noncomputable section
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

/-- The radial potential restricted to the first coordinate axis. -/
def coreRadialProfile (p : CuspParameters) (r : ℝ) : ℝ :=
  p.core (r • coordinateVector 0)

private theorem norm_first_coordinateVector : ‖coordinateVector 0‖ = 1 := by
  simp [coordinateVector, PiLp.norm_single]

theorem coreRadialProfile_contDiff {p : CuspParameters} (hr : 0 < p.r₀) :
    ContDiff ℝ ∞ p.coreRadialProfile :=
  (core_contDiff hr).comp (contDiff_id.smul contDiff_const)

/-- The signed-axis profile recovers the core at every point. -/
theorem core_eq_coreRadialProfile_norm (p : CuspParameters) (x : Plane) :
    p.core x = p.coreRadialProfile ‖x‖ := by
  simp only [coreRadialProfile, core, norm_smul, Real.norm_eq_abs,
    norm_first_coordinateVector, mul_one, abs_of_nonneg (norm_nonneg x)]

theorem coreRadialProfile_zero {p : CuspParameters} (hr : 0 < p.r₀) :
    p.coreRadialProfile 0 = -1 := by
  simpa only [coreRadialProfile, zero_smul] using core_zero hr

theorem coreRadialProfile_gt_neg_one (p : CuspParameters) {r : ℝ} (hr : r ≠ 0) :
    -1 < p.coreRadialProfile r := by
  apply core_gt_neg_one
  apply norm_pos_iff.mp
  simpa only [norm_smul, Real.norm_eq_abs, norm_first_coordinateVector, mul_one] using
    abs_pos.mpr hr

theorem coreRadialProfile_unique_minimum {p : CuspParameters} (hr : 0 < p.r₀) :
    p.coreRadialProfile 0 = -1 ∧
      ∀ r : ℝ, r ≠ 0 → p.coreRadialProfile 0 < p.coreRadialProfile r := by
  refine ⟨coreRadialProfile_zero hr, ?_⟩
  intro r hrne
  rw [coreRadialProfile_zero hr]
  exact coreRadialProfile_gt_neg_one p hrne

theorem coreRadialProfile_hasCompactSupport (p : CuspParameters) :
    HasCompactSupport p.coreRadialProfile := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -p.r₀) (b := p.r₀))
  intro r hr
  have hr' : p.coreRadialProfile r ≠ 0 := hr
  have hlt : |r| < p.r₀ := by
    by_contra h
    apply hr'
    simp only [coreRadialProfile, core, norm_smul, Real.norm_eq_abs,
      norm_first_coordinateVector, mul_one, if_neg h]
  exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩

theorem coreRadialProfile_eventuallyEq_squaredProfile {p : CuspParameters}
    (hr : 0 < p.r₀) :
    p.coreRadialProfile =ᶠ[𝓝 0] (fun r : ℝ => p.radialCoreProfile (r ^ 2)) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with r hball
  have hlt : |r| < p.r₀ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hball
  simp only [coreRadialProfile, core, norm_smul, Real.norm_eq_abs,
    norm_first_coordinateVector, mul_one, if_pos hlt, sq_abs, radialCoreProfile]

/-- The exact radial Hessian coefficient, obtained by composition with r². -/
theorem coreRadialProfile_second_derivative {p : CuspParameters} (hr : 0 < p.r₀) :
    iteratedDeriv 2 p.coreRadialProfile 0 = 2 / p.r₀ ^ 2 := by
  have heq := coreRadialProfile_eventuallyEq_squaredProfile hr
  rw [heq.iteratedDeriv_eq 2]
  change iteratedDeriv 2 (p.radialCoreProfile ∘ fun r : ℝ => r ^ 2) 0 = _
  have hq : ContDiffAt ℝ 2 (fun r : ℝ => r ^ 2) 0 := contDiffAt_id.pow 2
  have hg : ContDiffAt ℝ 2 p.radialCoreProfile ((0 : ℝ) ^ 2) := by
    simpa using radialCoreProfile_contDiffAt_zero hr
  have hq1 : deriv (fun r : ℝ => r ^ 2) 0 = 0 := by simp
  have hq2 : iteratedDeriv 2 (fun r : ℝ => r ^ 2) 0 = 2 := by norm_num
  rw [iteratedDeriv_comp_two (f := fun r : ℝ => r ^ 2) hg hq, hq1, hq2]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
  rw [(radialCoreProfile_hasDerivAt_zero hr).deriv]
  ring

theorem coreRadialProfile_second_derivative_pos {p : CuspParameters} (hr : 0 < p.r₀) :
    0 < iteratedDeriv 2 p.coreRadialProfile 0 := by
  rw [coreRadialProfile_second_derivative hr]
  exact div_pos (by norm_num) (sq_pos_of_pos hr)

end InfiniteZero.CuspParameters
