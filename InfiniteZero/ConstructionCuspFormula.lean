import InfiniteZero.ConstructionCuspSmoothAway
import InfiniteZero.LogFlat

/-!
# A global formula for the cusp

The support conditions on the cutoffs make the chart indicators redundant.
The singular-looking tangential quotient is multiplied by the zero-extended
log-flat profile, including on the entire nonpositive normal half-plane.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

theorem cuspPlus_eq_logFlat_formula {p : CuspParameters} (h : p.BasicConditions)
    (x : Plane) :
    p.cuspPlus x = (-p.a * p.χa (p.normalCoordinate x)) *
      (logFlat p.β p.tStar (p.normalCoordinate x) *
        p.χb (p.tangentCoordinate x / p.normalCoordinate x ^ 2)) := by
  by_cases ht : 0 < p.normalCoordinate x
  · rw [cuspPlus_eq_formula_of_normal_pos h ht, logFlat_of_pos _ _ ht]
    ring
  · simp [cuspPlus, ht, logFlat_of_nonpos _ _ (le_of_not_gt ht)]

end InfiniteZero.CuspParameters
