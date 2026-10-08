import InfiniteZero.LandauHeatKernelBounds

/-!
# The positive-time boundary at infinity

The spatial mass bound for the heat kernel bounds its action on every
bounded source. A positive exponential time weight then gives a zero
boundary term at infinity in the Laplace-transform identity.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace InfiniteZero

/-- The heat action is bounded by any uniform bound for its source. -/
theorem norm_landauHeatAction_le {B t : ℝ} (hB : 0 < B) (ht : 0 < t)
    {f : Wavefunction} (hf : Continuous f) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ y, ‖f y‖ ≤ M) (x : Plane) :
    ‖landauHeatAction B t f x‖ ≤ M :=
  (norm_integral_le_integral_norm _).trans
    (integral_norm_landauHeatKernel_mul_bounded_le hB ht x hf hM hbound)

/-- The exponentially weighted heat action vanishes at infinite time. -/
theorem landauHeatAction_weighted_tendsto_atTop {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) {f : Wavefunction}
    (hf : IsTestFunction f) (x : Plane) :
    Tendsto (fun t : ℝ => (Real.exp (-ρ * t) : ℂ) * landauHeatAction B t f x)
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hb⟩ :=
    (hf.2.isCompact_range hf.1.continuous).isBounded.exists_pos_norm_le
  have he : Tendsto (fun t : ℝ => Real.exp (-ρ * t) * M) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop_of_neg
        (neg_neg_of_pos hρ))).mul_const M
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (norm_landauHeatAction_le hB ht hf.1.continuous hM.le
      (fun y => hb _ (mem_range_self y)) x) (Real.exp_pos _).le

end InfiniteZero
