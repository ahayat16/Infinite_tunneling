import InfiniteZero.CoreRadialHypotheses

/-!
# Monotonicity and a fixed inner reserve of the radial core

The global smooth-glue formula includes the zero extension at the edge of
the core. The only geometric hypothesis is positivity of the core radius;
the magnetic field may be any real number.
-/

noncomputable section
open Set
open scoped Topology

namespace InfiniteZero.CuspParameters

/-- The signed radial profile has the same smooth-glue formula as the core. -/
theorem coreRadialProfile_eq_expNegInvGlue {p : CuspParameters}
    (hr : 0 < p.r₀) (r : ℝ) :
    p.coreRadialProfile r =
      -Real.exp 1 * expNegInvGlue ((p.r₀ ^ 2 - r ^ 2) / p.r₀ ^ 2) := by
  unfold coreRadialProfile
  rw [core_eq_expNegInvGlue p hr]
  simp [norm_smul, coordinateVector, PiLp.norm_single]

/-- The core increases from its minimum to its zero exterior value. -/
theorem coreRadialProfile_monotoneOn {p : CuspParameters} (hr : 0 < p.r₀) :
    MonotoneOn p.coreRadialProfile (Ici 0) := by
  intro x hx y hy hxy
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).mpr hxy
  rw [coreRadialProfile_eq_expNegInvGlue hr x,
    coreRadialProfile_eq_expNegInvGlue hr y]
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (Real.exp_pos 1).le)
  apply expNegInvGlue.monotone
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg p.r₀)

/-- Adding the radial magnetic oscillator preserves monotonicity. -/
theorem effectiveCoreRadialProfile_monotoneOn {p : CuspParameters}
    (hr : 0 < p.r₀) (b : ℝ) :
    MonotoneOn (fun r : ℝ => b ^ 2 * r ^ 2 / 4 + p.coreRadialProfile r) (Ici 0) := by
  intro x hx y hy hxy
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).mpr hxy
  apply add_le_add _ (coreRadialProfile_monotoneOn hr hx hy hxy)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (sq_nonneg b)) (by norm_num)

/-- A global lower bound, also valid for signed radial coordinates. -/
theorem neg_one_le_effectiveCoreRadialProfile (p : CuspParameters) (b r : ℝ) :
    -1 ≤ b ^ 2 * r ^ 2 / 4 + p.coreRadialProfile r := by
  have hc : -1 ≤ p.coreRadialProfile r := (core_range p (r • coordinateVector 0)).1
  have hb : 0 ≤ b ^ 2 * r ^ 2 / 4 := by positivity
  linarith

/-- A fixed neighborhood of the minimum has depth at least one half.
The radius is chosen from the core alone, before any coupling parameter. -/
theorem exists_coreRadialProfile_neg_half {p : CuspParameters} (hr : 0 < p.r₀) :
    ∃ δ > 0, ∀ r ∈ Icc 0 δ, (1 / 2 : ℝ) ≤ -p.coreRadialProfile r := by
  have hzero : p.coreRadialProfile 0 < -(1 / 2 : ℝ) := by
    rw [coreRadialProfile_zero hr]
    norm_num
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), p.coreRadialProfile r < -(1 / 2 : ℝ) :=
    (coreRadialProfile_contDiff hr).continuous.continuousAt.eventually_lt_const hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε / 2, half_pos hε, fun r hrange => ?_⟩
  have hmem : r ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hrange.1]
    linarith [hrange.2]
  have hlt : p.coreRadialProfile r < -(1 / 2 : ℝ) := hball hmem
  linarith

end InfiniteZero.CuspParameters
