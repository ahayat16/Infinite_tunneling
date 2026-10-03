import InfiniteZero.Construction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smoothness of the explicit radial core

The zero extension in the manuscript is exactly a rescaled instance of
Mathlib's `expNegInvGlue`.  Its established flatness at zero therefore proves
smoothness at the boundary of the core ball as well as in its interior.
-/

noncomputable section

open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- An exact global formula, including the boundary and exterior of the core. -/
theorem core_eq_expNegInvGlue (p : CuspParameters) (hr : 0 < p.r₀) (x : Plane) :
    p.core x = -Real.exp 1 * expNegInvGlue ((p.r₀ ^ 2 - ‖x‖ ^ 2) / p.r₀ ^ 2) := by
  have hr2 : 0 < p.r₀ ^ 2 := sq_pos_of_pos hr
  by_cases hx : ‖x‖ < p.r₀
  · have hd : 0 < p.r₀ ^ 2 - ‖x‖ ^ 2 := by
      nlinarith [norm_nonneg x]
    have hz : 0 < (p.r₀ ^ 2 - ‖x‖ ^ 2) / p.r₀ ^ 2 := div_pos hd hr2
    rw [core, if_pos hx, expNegInvGlue, if_neg (not_le_of_gt hz), neg_mul,
      ← Real.exp_add]
    congr 2
    field_simp [hd.ne', hr2.ne']
    ring
  · have hn : p.r₀ ≤ ‖x‖ := not_lt.mp hx
    have hd : p.r₀ ^ 2 - ‖x‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg x]
    have hz : (p.r₀ ^ 2 - ‖x‖ ^ 2) / p.r₀ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hd hr2.le
    rw [core, if_neg hx, expNegInvGlue.zero_of_nonpos hz, mul_zero]

/-- The radial reference well is smooth across its zero-extension boundary. -/
theorem core_contDiff {p : CuspParameters} (hr : 0 < p.r₀) :
    ContDiff ℝ ∞ p.core := by
  have harg : ContDiff ℝ ∞ (fun x : Plane => (p.r₀ ^ 2 - ‖x‖ ^ 2) / p.r₀ ^ 2) :=
    (contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _
  have hglue : ContDiff ℝ ∞
      (fun x : Plane => expNegInvGlue ((p.r₀ ^ 2 - ‖x‖ ^ 2) / p.r₀ ^ 2)) :=
    expNegInvGlue.contDiff.comp harg
  have hscaled : ContDiff ℝ ∞ (fun x : Plane =>
      -Real.exp 1 * expNegInvGlue ((p.r₀ ^ 2 - ‖x‖ ^ 2) / p.r₀ ^ 2)) :=
    contDiff_const.mul hglue
  convert hscaled using 1
  funext x
  exact core_eq_expNegInvGlue p hr x

end InfiniteZero.CuspParameters
