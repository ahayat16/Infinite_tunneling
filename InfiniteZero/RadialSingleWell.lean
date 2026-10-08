import InfiniteZero.CoreRadialHypotheses
import InfiniteZero.ConstructionCompact

/-!
# Hypotheses for radial single-well harmonic approximation

`RadialSingleWell` records the smoothness, compact support, radiality and
nondegenerate unique negative minimum used in the classical unit-field
spectral theorem. The explicit core divided by the square of any positive
magnetic field satisfies these hypotheses.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

/-- A smooth radial well with a unique nondegenerate negative minimum at the
origin. Nondegeneracy is expressed by the second derivative of the signed
radial profile along the first coordinate axis. -/
structure RadialSingleWell (V : Potential) : Prop where
  smooth : ContDiff ℝ ∞ V
  compact_support : HasCompactSupport V
  nonpos : ∀ x, V x ≤ 0
  minimum_neg : V 0 < 0
  strict_minimum : ∀ x, x ≠ 0 → V 0 < V x
  radial : ∀ x, V x = V (‖x‖ • coordinateVector 0)
  radial_second_pos :
    0 < iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0

namespace CuspParameters

/-- Dividing the explicit core by `b²` preserves all radial single-well
hypotheses. This is the potential used when reducing a positive magnetic
field `b` to the unit-field spectral theorem. -/
theorem core_div_sq_radialSingleWell {p : CuspParameters} {b : ℝ}
    (hb : 0 < b) (hr : 0 < p.r₀) :
    RadialSingleWell (fun x => p.core x / b ^ 2) where
  smooth := (core_contDiff hr).div_const _
  compact_support := by
    simpa only [div_eq_mul_inv] using
      (core_hasCompactSupport p).mul_right (f' := fun _ => (b ^ 2)⁻¹)
  nonpos x := div_nonpos_of_nonpos_of_nonneg (core_range p x).2 (sq_nonneg b)
  minimum_neg := by
    rw [core_zero hr]
    exact div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hb)
  strict_minimum x hx := by
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hb)).mpr
    rw [core_zero hr]
    exact core_gt_neg_one hx
  radial x := by
    rw [core_eq_coreRadialProfile_norm p x]
    rfl
  radial_second_pos := by
    change 0 < iteratedDeriv 2 (fun r => p.coreRadialProfile r / b ^ 2) 0
    rw [iteratedDeriv_div_const]
    exact div_pos (coreRadialProfile_second_derivative_pos hr) (sq_pos_of_pos hb)

end CuspParameters

end InfiniteZero
