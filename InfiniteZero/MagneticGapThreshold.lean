import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform lower bounds from the unit-field gap asymptotic

If the unit-field spectral gap divided by its coupling tends to a positive
number `δ`, it is eventually at least `δ / 2`. At field parameter `b > 0`,
the unit-field coupling is `b * λ`; the resulting gap is bounded below by
`(b * δ / 2) * λ`. The choice of a positive threshold and this change of
constants are proved here independently of any spectral admission.
-/

open Filter
open scoped Topology

namespace InfiniteZero

/-- A positive limiting gap ratio gives a uniform lower bound after the
unit-field change of coupling. The threshold is explicitly chosen positive. -/
theorem exists_pos_threshold_unitField_lower {g : ℝ → ℝ} {δ b : ℝ}
    (hδ : 0 < δ) (hg : Tendsto g atTop (𝓝 δ)) (hb : 0 < b) :
    ∃ T : ℝ, 0 < T ∧ ∀ coupling : ℝ, T ≤ coupling → δ / 2 ≤ g (b * coupling) := by
  obtain ⟨R, hR⟩ := eventually_atTop.1
    (hg.eventually_const_le (half_lt_self hδ))
  refine ⟨max 1 (R / b), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro coupling hc
  apply hR
  have hdiv : R / b ≤ coupling := (le_max_right _ _).trans hc
  simpa only [mul_comm] using (div_le_iff₀ hb).mp hdiv

/-- Multiplying the eventual bound for the gap ratio by the positive
unit-field coupling gives a linear gap with constant `b * δ / 2`. -/
theorem exists_pos_threshold_unitField_linear_gap {g : ℝ → ℝ} {δ b : ℝ}
    (hδ : 0 < δ) (hg : Tendsto g atTop (𝓝 δ)) (hb : 0 < b) :
    ∃ T : ℝ, 0 < T ∧ ∀ coupling : ℝ, T ≤ coupling →
      (b * δ / 2) * coupling ≤ g (b * coupling) * (b * coupling) := by
  obtain ⟨T, hT, hbound⟩ := exists_pos_threshold_unitField_lower hδ hg hb
  refine ⟨T, hT, ?_⟩
  intro coupling hc
  have hcoupling : 0 < coupling := hT.trans_le hc
  calc
    (b * δ / 2) * coupling = (δ / 2) * (b * coupling) := by ring
    _ ≤ g (b * coupling) * (b * coupling) :=
      mul_le_mul_of_nonneg_right (hbound coupling hc) (by positivity)

end InfiniteZero
