import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.LeftRight

/-!
# Integration of a derivative between positive time zero and infinity

The value assigned to the original function at zero is irrelevant: the
boundary term is its right-hand limit.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InfiniteZero

/-- Fundamental theorem of calculus on positive times, with the value at
zero supplied by a right-hand limit. -/
theorem integral_Ioi_derivative_of_boundary_limits {F D : ℝ → ℂ} {a b : ℂ}
    (hD : ∀ t : ℝ, 0 < t → HasDerivAt F (D t) t)
    (hDI : IntegrableOn D (Ioi 0))
    (hzero : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 a))
    (htop : Tendsto F atTop (𝓝 b)) :
    (∫ t in Ioi (0 : ℝ), D t) = b - a := by
  let G : ℝ → ℂ := fun t => if t = 0 then a else F t
  have hG0 : G 0 = a := by simp [G]
  have hGeq : ∀ t : ℝ, 0 < t → G t = F t := by
    intro t ht
    simp [G, ht.ne']
  have hGc : ContinuousWithinAt G (Ici 0) 0 := by
    apply continuousWithinAt_Ioi_iff_Ici.mp
    change Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0))
    rw [hG0]
    apply hzero.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hGeq t ht).symm
  have hGd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt G (D t) t := by
    intro t ht
    apply (hD t ht).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hGeq s hs
  have hGt : Tendsto G atTop (𝓝 b) := by
    apply htop.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hGeq t ht).symm
  simpa [hG0] using integral_Ioi_of_hasDerivAt_of_tendsto hGc hGd hDI hGt

end InfiniteZero
