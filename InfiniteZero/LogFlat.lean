import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rapid decay of the log-flat cusp profile

The zero extension is a genuine function on the whole real line.  Its right
limit, even after multiplying by arbitrary inverse powers and logarithmic
powers, is proved from Gaussian asymptotics after a logarithmic change of
variables.
-/

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace InfiniteZero

/-- The scalar factor in the one-sided log-flat cusp profile. -/
def logFlat (β tStar t : ℝ) : ℝ :=
  if 0 < t then Real.exp (-β * (Real.log (tStar / t)) ^ 2) else 0

@[simp] theorem logFlat_of_nonpos (β tStar : ℝ) {t : ℝ} (ht : t ≤ 0) :
    logFlat β tStar t = 0 := by simp [logFlat, not_lt.mpr ht]

theorem logFlat_of_pos (β tStar : ℝ) {t : ℝ} (ht : 0 < t) :
    logFlat β tStar t = Real.exp (-β * (Real.log (tStar / t)) ^ 2) := by
  simp [logFlat, ht]

/-- A Gaussian with any linear correction dominates every polynomial power. -/
theorem tendsto_pow_mul_exp_quadratic {β : ℝ} (hβ : 0 < β) (A : ℝ) (N : ℕ) :
    Tendsto (fun y : ℝ => y ^ N * Real.exp (-β * y ^ 2 + A * y)) atTop (𝓝 0) := by
  have h := (rexp_neg_quadratic_isLittleO_rpow_atTop (neg_neg_of_pos hβ)
    A (-(N : ℝ))).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  simp [Real.rpow_neg hy.le, Real.rpow_natCast, mul_comm]

/-- The convenient positive logarithmic weight has the same Gaussian decay. -/
theorem tendsto_one_add_abs_pow_mul_exp_quadratic {β : ℝ} (hβ : 0 < β)
    (A : ℝ) (N : ℕ) :
    Tendsto (fun y : ℝ => (1 + |y|) ^ N * Real.exp (-β * y ^ 2 + A * y))
      atTop (𝓝 0) := by
  have hshift : Tendsto (fun y : ℝ => y + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have h := ((tendsto_pow_mul_exp_quadratic hβ (A + 2 * β) N).comp hshift).const_mul
    (Real.exp (-β - A))
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  dsimp only [Function.comp_apply]
  rw [abs_of_nonneg hy]
  have hexp : Real.exp (-β - A) *
      Real.exp (-β * (y + 1) ^ 2 + (A + 2 * β) * (y + 1)) =
      Real.exp (-β * y ^ 2 + A * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-β - A) * ((y + 1) ^ N *
        Real.exp (-β * (y + 1) ^ 2 + (A + 2 * β) * (y + 1))) =
      (1 + y) ^ N * (Real.exp (-β - A) *
        Real.exp (-β * (y + 1) ^ 2 + (A + 2 * β) * (y + 1))) := by ring
    _ = (1 + y) ^ N * Real.exp (-β * y ^ 2 + A * y) := by rw [hexp]

theorem tendsto_log_tStar_div_nhdsGT_zero {tStar : ℝ} (hStar : 0 < tStar) :
    Tendsto (fun t : ℝ => Real.log (tStar / t)) (𝓝[>] 0) atTop := by
  apply Real.tendsto_log_atTop.comp
  simpa only [div_eq_mul_inv] using
    (tendsto_inv_nhdsGT_zero.const_mul_atTop hStar)

/-- Every inverse power of the normal variable and every logarithmic power
are absorbed by the log-flat factor. The two exponents are independent. -/
theorem tendsto_logFlat_weighted {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (N M : ℕ) :
    Tendsto (fun t : ℝ => (t ^ N)⁻¹ * (1 + |Real.log (tStar / t)|) ^ M *
      logFlat β tStar t) (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_one_add_abs_pow_mul_exp_quadratic hβ (N : ℝ) M).comp
    (tendsto_log_tStar_div_nhdsGT_zero hStar)).const_mul ((tStar ^ N)⁻¹)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  rw [logFlat_of_pos β tStar htpos]
  dsimp only [Function.comp_apply]
  have hp : (t ^ N)⁻¹ = (tStar ^ N)⁻¹ * Real.exp ((N : ℝ) * Real.log (tStar / t)) := by
    rw [Real.exp_nat_mul, Real.exp_log (div_pos hStar htpos), div_pow]
    field_simp [ne_of_gt hStar, ne_of_gt htpos]
  rw [hp, Real.exp_add]
  ring

theorem tendsto_logFlat_nhdsGT_zero {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar) :
    Tendsto (logFlat β tStar) (𝓝[>] 0) (𝓝 0) := by
  simpa using tendsto_logFlat_weighted hβ hStar 0 0

/-- The weighted limit also holds from both sides, because of the zero extension. -/
theorem tendsto_logFlat_weighted_zero {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (N M : ℕ) :
    Tendsto (fun t : ℝ => (t ^ N)⁻¹ * (1 + |Real.log (tStar / t)|) ^ M *
      logFlat β tStar t) (𝓝 0) (𝓝 0) := by
  let f : ℝ → ℝ := fun t => (t ^ N)⁻¹ * (1 + |Real.log (tStar / t)|) ^ M *
    logFlat β tStar t
  have hf0 : f 0 = 0 := by simp [f, logFlat]
  have hc : ContinuousAt f 0 := by
    apply continuousAt_iff_continuous_left'_right'.2
    constructor
    · change Tendsto f (𝓝[<] 0) (𝓝 (f 0))
      rw [hf0]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp [f, logFlat_of_nonpos β tStar (le_of_lt ht)]
    · change Tendsto f (𝓝[>] 0) (𝓝 (f 0))
      rw [hf0]
      exact tendsto_logFlat_weighted hβ hStar N M
  simpa only [hf0] using hc.tendsto

/-- Flatness in little-o form, including the value at the origin. -/
theorem logFlat_isLittleO_pow {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar) (N : ℕ) :
    logFlat β tStar =o[𝓝 0] (fun t : ℝ => t ^ N) := by
  have hzero (t : ℝ) (ht : t ^ N = 0) : logFlat β tStar t = 0 := by
    have ht0 : t = 0 := eq_zero_of_pow_eq_zero ht
    simp [ht0, logFlat]
  apply (isLittleO_iff_tendsto hzero).2
  simpa [div_eq_mul_inv, mul_comm] using tendsto_logFlat_weighted_zero hβ hStar N 0

theorem continuousAt_logFlat_zero {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar) :
    ContinuousAt (logFlat β tStar) 0 := by
  have h := tendsto_logFlat_weighted_zero hβ hStar 0 0
  change Tendsto (logFlat β tStar) (𝓝 0) (𝓝 (logFlat β tStar 0))
  rw [logFlat_of_nonpos β tStar (le_refl 0)]
  simpa only [pow_zero, inv_one, mul_one, one_mul] using h

/-- In particular, the zero extension has derivative exactly zero at the tip. -/
theorem hasDerivAt_logFlat_zero {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar) :
    HasDerivAt (logFlat β tStar) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h := (tendsto_logFlat_weighted_zero hβ hStar 1 0).mono_left
    (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simpa only [pow_one, pow_zero, mul_one, zero_add,
    logFlat_of_nonpos β tStar (le_refl 0), sub_zero, smul_eq_mul] using h

end InfiniteZero
