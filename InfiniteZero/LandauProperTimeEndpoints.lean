import InfiniteZero.LandauKernel

/-!
# Endpoint limits of the proper-time integrand

The singular hyperbolic prefactor is absorbed by the exponential at positive
radius. Both endpoint values therefore vanish for positive physical parameters.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

/-- At the singular endpoint, inverse sinh tends to positive infinity. -/
theorem tendsto_inv_sinh_mul_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun τ : ℝ => (Real.sinh (b * τ))⁻¹) (𝓝[>] 0) atTop := by
  apply tendsto_inv_nhdsGT_zero.comp
  apply tendsto_nhdsWithin_iff.2
  constructor
  · simpa using (Real.continuous_sinh.continuousAt.comp
      (continuousAt_const.mul continuousAt_id) :
      ContinuousAt (fun τ : ℝ => Real.sinh (b * τ)) 0).tendsto.mono_left
        nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact Real.sinh_pos_iff.2 (mul_pos hb hτ)

/-- The Gaussian factor defeats the singular prefactor at zero proper time.
No sign restriction on the energy is needed at this endpoint. -/
theorem tendsto_landauIntegrand_zero {b h r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hr : 0 < r) (E : ℝ) :
    Tendsto (landauIntegrand b h E r) (𝓝[>] 0) (𝓝 0) := by
  let c := b * r ^ 2 / (4 * h)
  let y := fun τ : ℝ => (Real.sinh (b * τ))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hy : Tendsto y (𝓝[>] 0) atTop := tendsto_inv_sinh_mul_zero hb
  have hpoly : Tendsto (fun τ => y τ * Real.exp (-(c * y τ)))
      (𝓝[>] 0) (𝓝 0) := by
    have ht := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (hy.const_mul_atTop hc)).const_mul c⁻¹
    simpa only [Function.comp_apply, pow_one, mul_zero, ← mul_assoc,
      inv_mul_cancel₀ hc.ne', one_mul] using ht
  have hexp : Tendsto (fun τ : ℝ => Real.exp ((-E / h) * τ))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using (Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id) :
      ContinuousAt (fun τ : ℝ => Real.exp ((-E / h) * τ)) 0).tendsto.mono_left
        nhdsWithin_le_nhds
  apply squeeze_zero' (g := fun τ =>
    (y τ * Real.exp (-(c * y τ))) * Real.exp ((-E / h) * τ))
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (landauIntegrand_pos hb hτ h E r).le
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hypos : 0 < y τ := inv_pos.2 (Real.sinh_pos_iff.2 (mul_pos hb hτ))
    have hcosh := Real.one_le_cosh (b * τ)
    have hfactor : landauIntegrand b h E r τ =
        (y τ * Real.exp (-(c * Real.cosh (b * τ) * y τ))) *
          Real.exp ((-E / h) * τ) := by
      unfold landauIntegrand properTimePhase
      dsimp [c, y]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ hypos.le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_pos hc hypos).le (sub_nonneg.mpr hcosh)]
  · simpa using hpoly.mul hexp

/-- Positive energy gives exponential decay at infinite proper time. -/
theorem tendsto_landauIntegrand_atTop {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    Tendsto (landauIntegrand b h E r) atTop (𝓝 0) := by
  have hneg : -E / h < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hE) hh
  have ht : Tendsto (fun τ : ℝ => Real.exp ((-E / h) * τ)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
  apply squeeze_zero' (g := fun τ =>
    (4 * h / (b * r ^ 2)) * Real.exp ((-E / h) * τ))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    exact (landauIntegrand_pos hb hτ h E r).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    exact landauIntegrand_le_exp hb hh hr hτ E
  · simpa using ht.const_mul (4 * h / (b * r ^ 2))

/-- The definition at zero agrees with the right endpoint limit. -/
theorem continuousWithinAt_landauIntegrand_zero {b h r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hr : 0 < r) (E : ℝ) :
    ContinuousWithinAt (landauIntegrand b h E r) (Ici 0) 0 := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  simpa [ContinuousWithinAt, landauIntegrand] using
    tendsto_landauIntegrand_zero hb hh hr E

end InfiniteZero
