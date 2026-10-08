import InfiniteZero.LandauKernel

/-!
# Bounds on the exterior Landau coefficient from one positive value

The evaluation radius is the semiclassical parameter h. A lower bound on
Γ K(h), together with E ≥ 1/2, yields Γ ≥ c π h² / 2 and the corresponding
polynomial upper bound for its reciprocal. The sign of Γ is a conclusion.
-/

noncomputable section

namespace InfiniteZero

variable {b h E c Γ : ℝ}

theorem landau_coefficient_pos_of_value_lower
    (hb : 0 < b) (hh : 0 < h) (hEhalf : (1 / 2 : ℝ) ≤ E) (hc : 0 < c)
    (hvalue : c ≤ Γ * landauKernel b h E h) : 0 < Γ := by
  have hE : 0 < E := by linarith
  exact (mul_pos_iff_of_pos_right (landauKernel_pos hb hh hE hh)).mp
    (hc.trans_le hvalue)

theorem landau_coefficient_lower_of_value_lower
    (hb : 0 < b) (hh : 0 < h) (hEhalf : (1 / 2 : ℝ) ≤ E) (hc : 0 < c)
    (hvalue : c ≤ Γ * landauKernel b h E h) :
    (c * Real.pi / 2) * h ^ 2 ≤ Γ := by
  have hE : 0 < E := by linarith
  have hΓ := landau_coefficient_pos_of_value_lower hb hh hEhalf hc hvalue
  have hbound := mul_le_mul_of_nonneg_left (landauKernel_le hb hh hE hh) hΓ.le
  have hdiv : c ≤ Γ / (Real.pi * E * h ^ 2) := by
    simpa only [mul_one_div] using hvalue.trans hbound
  have hstrong := (le_div_iff₀ (show 0 < Real.pi * E * h ^ 2 by positivity)).mp hdiv
  calc
    (c * Real.pi / 2) * h ^ 2 = (c * Real.pi * h ^ 2) * (1 / 2) := by ring
    _ ≤ (c * Real.pi * h ^ 2) * E :=
      mul_le_mul_of_nonneg_left hEhalf (by positivity)
    _ ≤ Γ := by nlinarith only [hstrong]

theorem landau_coefficient_inv_le_of_value_lower
    (hb : 0 < b) (hh : 0 < h) (hEhalf : (1 / 2 : ℝ) ≤ E) (hc : 0 < c)
    (hvalue : c ≤ Γ * landauKernel b h E h) :
    Γ⁻¹ ≤ (2 / (c * Real.pi)) * (h⁻¹) ^ 2 := by
  have hlower := landau_coefficient_lower_of_value_lower hb hh hEhalf hc hvalue
  calc
    Γ⁻¹ ≤ ((c * Real.pi / 2) * h ^ 2)⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (show 0 < (c * Real.pi / 2) * h ^ 2 by positivity) hlower
    _ = (2 / (c * Real.pi)) * (h⁻¹) ^ 2 := by
      field_simp

end InfiniteZero
