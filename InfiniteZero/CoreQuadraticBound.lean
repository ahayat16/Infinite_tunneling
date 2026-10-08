import InfiniteZero.Construction

/-!
# A quadratic upper bound for the radial core

The explicit reference well of `eq:explicit-core` satisfies
`0 ≤ v°(x) + 1 ≤ (2 / r₀²) |x|²`. This elementary bound is sufficient for
the variational upper bound on its ground energy; it does not use harmonic
approximation or any spectral admission.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

/-- The explicit radial core lies below a quadratic well of depth one.
Inside `|x|² ≤ r₀²/2`, this follows from `1 - exp (-u) ≤ u`; outside,
the quadratic bound is at least one and `core ≤ 0`. -/
theorem core_add_one_le_quadratic {p : CuspParameters} (hr : 0 < p.r₀)
    (x : Plane) : p.core x + 1 ≤ (2 / p.r₀ ^ 2) * ‖x‖ ^ 2 := by
  have hr2 : 0 < p.r₀ ^ 2 := sq_pos_of_pos hr
  by_cases hx : ‖x‖ ^ 2 ≤ p.r₀ ^ 2 / 2
  · have hden : 0 < p.r₀ ^ 2 - ‖x‖ ^ 2 := by linarith
    have hxr : ‖x‖ < p.r₀ := by nlinarith [norm_nonneg x]
    have hquot : ‖x‖ ^ 2 / (p.r₀ ^ 2 - ‖x‖ ^ 2) ≤
        (2 / p.r₀ ^ 2) * ‖x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hr2]
      nlinarith [mul_nonneg (sq_nonneg ‖x‖) (show 0 ≤ p.r₀ ^ 2 - 2 * ‖x‖ ^ 2 by
        linarith)]
    rw [core, if_pos hxr]
    have hexp := Real.add_one_le_exp (-(‖x‖ ^ 2 / (p.r₀ ^ 2 - ‖x‖ ^ 2)))
    linarith
  · have hquad : 1 ≤ (2 / p.r₀ ^ 2) * ‖x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr2]
      linarith
    linarith [(core_range p x).2]

/-- Both sides of the quadratic comparison used in the energy estimate. -/
theorem core_add_one_bounds {p : CuspParameters} (hr : 0 < p.r₀) (x : Plane) :
    0 ≤ p.core x + 1 ∧ p.core x + 1 ≤ (2 / p.r₀ ^ 2) * ‖x‖ ^ 2 :=
  ⟨by linarith [(core_range p x).1], core_add_one_le_quadratic hr x⟩

end InfiniteZero.CuspParameters
