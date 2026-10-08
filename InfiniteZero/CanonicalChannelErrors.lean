import InfiniteZero.CuspTangentialMass
import InfiniteZero.LogFlat
import InfiniteZero.SeparationCertificate

/-! The two scalar relative bounds used in the canonical channel assembly. -/

noncomputable section
open Filter
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem tendsto_active_scattered_relative_rate
    {p : CuspParameters} (hp : p.BasicConditions) (L C : ℝ) :
    Tendsto (fun coupling : ℝ => (C / p.activeTangentialLeadingCoefficient L) *
      Real.exp (-(p.β / 8) * (Real.log coupling) ^ 2)) atTop (𝓝 0) := by
  have hβ : 0 < p.β / 8 := div_pos hp.β_pos (by norm_num)
  have hg := (tendsto_pow_mul_exp_quadratic hβ 0 0).comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, pow_zero, one_mul, zero_mul, add_zero, mul_zero] using
    hg.const_mul (C / p.activeTangentialLeadingCoefficient L)

theorem tendsto_inactive_relative_rate
    {p : CuspParameters} (hp : p.BasicConditions) (L C : ℝ) :
    Tendsto (fun coupling : ℝ => (C / p.activeTangentialLeadingCoefficient L) *
      Real.exp (-15 * p.hopMargin * coupling)) atTop (𝓝 0) := by
  have hd : -15 * p.hopMargin < 0 := by linarith [hopMargin_pos hp]
  have he := Real.tendsto_exp_atBot.comp
    ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop_of_neg hd)
  simpa only [Function.comp_def, mul_zero] using
    he.const_mul (C / p.activeTangentialLeadingCoefficient L)

end InfiniteZero.CuspParameters
