import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Harmonic level asymptotics in the unscaled coupling

Subtracting two first-order semiclassical expansions cancels the common
minimum value. Substitution `h = coupling⁻¹` gives the limiting gap divided
by the unscaled coupling.
-/

open Filter
open scoped Topology

namespace InfiniteZero

/-- The classical `O(h^(3/2))` remainder bound implies its first-order
coefficient limit. The factor `h * sqrt h` is divided by the positive `h`. -/
theorem tendsto_firstOrder_of_harmonic_remainder
    {e : ℝ → ℝ} {V₀ μ C h₀ : ℝ} (hh₀ : 0 < h₀) (_hC : 0 ≤ C)
    (hbound : ∀ h : ℝ, 0 < h → h ≤ h₀ →
      |e h - V₀ - h * μ| ≤ C * h * Real.sqrt h) :
    Tendsto (fun h => (e h - V₀) / h) (𝓝[>] (0 : ℝ)) (𝓝 μ) := by
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < h₀ :=
    nhdsWithin_le_nhds (gt_mem_nhds hh₀)
  have hestimate : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ‖(e h - V₀) / h - μ‖ ≤ C * Real.sqrt h := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hle
    have hp : 0 < h := hh
    have heq : (e h - V₀) / h - μ = (e h - V₀ - h * μ) / h := by
      field_simp
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_assoc, mul_comm h (Real.sqrt h)] using hbound h hp hle.le
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun h => norm_nonneg _)) hestimate
    (by simpa only [mul_zero] using hsqrt.const_mul C)

/-- Two first-order level asymptotics give the gap ratio at large coupling.
The common potential minimum cancels before taking the limit. -/
theorem tendsto_coupling_gap_of_harmonic_levels
    {e₁ e₂ : ℝ → ℝ} {V₀ μ₁ μ₂ : ℝ}
    (h₁ : Tendsto (fun h => (e₁ h - V₀) / h) (𝓝[>] (0 : ℝ)) (𝓝 μ₁))
    (h₂ : Tendsto (fun h => (e₂ h - V₀) / h) (𝓝[>] (0 : ℝ)) (𝓝 μ₂)) :
    Tendsto (fun coupling : ℝ => coupling * (e₂ coupling⁻¹ - e₁ coupling⁻¹))
      atTop (𝓝 (μ₂ - μ₁)) := by
  have h := (h₂.sub h₁).comp tendsto_inv_atTop_nhdsGT_zero
  convert h using 1
  ext coupling
  simp only [Function.comp_apply, div_inv_eq_mul]
  ring

end InfiniteZero
