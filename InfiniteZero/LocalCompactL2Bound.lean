import InfiniteZero.GenericCompactL2Bound

/-!
# Local L² bounds on bounded measurable regions

The indicator is applied after the function has been formed. It is never
differentiated. A pointwise bound only on the region suffices for genuine
L² membership and a mass estimate.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

theorem memLp_indicator_of_bound_on_subset_closedBall
    {F : Wavefunction} {s : Set Plane} {R B : ℝ}
    (hF : AEStronglyMeasurable F volume) (hs : MeasurableSet s)
    (hsR : s ⊆ Metric.closedBall (0 : Plane) R)
    (hB : 0 ≤ B) (hbound : ∀ x ∈ s, ‖F x‖ ≤ B) :
    MemLp (s.indicator F) 2 volume := by
  have hsupport : Function.support (s.indicator F) ⊆ Metric.closedBall (0 : Plane) R := by
    intro x hx
    by_cases hxs : x ∈ s
    · exact hsR hxs
    · exact False.elim (hx (by simp [hxs]))
  have hc : HasCompactSupport (s.indicator F) :=
    (isCompact_closedBall (0 : Plane) R).of_isClosed_subset isClosed_closure
      (closure_minimal hsupport Metric.isClosed_closedBall)
  apply hc.memLp_of_bound (hF.indicator hs) B
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using hbound x hx
    · simpa only [indicator_of_notMem hx, norm_zero] using hB

theorem mass_indicator_le_pi_mul_radius_sq_mul_bound_sq
    {F : Wavefunction} {s : Set Plane} {R B : ℝ}
    (hF : AEStronglyMeasurable F volume) (hs : MeasurableSet s)
    (hR : 0 ≤ R) (hsR : s ⊆ Metric.closedBall (0 : Plane) R)
    (hB : 0 ≤ B) (hbound : ∀ x ∈ s, ‖F x‖ ≤ B) :
    mass (s.indicator F) ≤ (Real.sqrt Real.pi * R * B) ^ 2 := by
  have hm := memLp_indicator_of_bound_on_subset_closedBall hF hs hsR hB hbound
  have hsupport : Function.support (s.indicator F) ⊆ Metric.closedBall (0 : Plane) R := by
    intro x hx
    by_cases hxs : x ∈ s
    · exact hsR hxs
    · exact False.elim (hx (by simp [hxs]))
  have hb (x : Plane) : ‖s.indicator F x‖ ≤ B := by
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using hbound x hx
    · simpa only [indicator_of_notMem hx, norm_zero] using hB
  have hmass := mass_le_pi_mul_radius_sq_mul_bound_sq hm hR hsupport hB hb
  simpa only [mul_pow, Real.sq_sqrt Real.pi_pos.le] using hmass

theorem mass_indicator_eq_setIntegral (s : Set Plane) (hs : MeasurableSet s)
    (F : Wavefunction) :
    mass (s.indicator F) = ∫ x in s, ‖F x‖ ^ 2 := by
  unfold mass
  have heq : (fun x => ‖s.indicator F x‖ ^ 2) = s.indicator (fun x => ‖F x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq, integral_indicator hs]

end InfiniteZero
