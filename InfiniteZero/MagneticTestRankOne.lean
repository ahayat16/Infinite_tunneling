import InfiniteZero.MagneticGraphLowerBound

/-!
# Operator rank-one bounds imply bounds for physical test functions

This is the reverse bridge to `IsMagneticRealization.rankOne_lower`.
Every test pair belongs to the specified closed graph, so no approximation
or new spectral input is needed in this direction.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

/-- A rank-one estimate on the actual operator domain applies to every
smooth compactly supported physical wavefunction. -/
theorem IsMagneticRealization.test_rankOne_lower_of_operator
    {b coupling c k E : ℝ} {V : Potential}
    (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {v : L2Space} {φ : Wavefunction} (hv : Represents v φ)
    (hbound : ∀ u : (magneticOperator b coupling V).domain,
      c * ‖(u : L2Space)‖ ^ 2 - k * ‖inner ℂ v (u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space) (magneticOperator b coupling V u)).re -
          E * ‖(u : L2Space)‖ ^ 2)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    c * mass ψ - k * ‖waveInner φ ψ‖ ^ 2 ≤
      magneticForm b coupling V ψ - E * mass ψ := by
  have hg := hψ.mem_magneticTestGraph b coupling hV
  have hc : (hψ.memLp.toLp ψ,
      (hψ.memLp_magneticHamiltonian b coupling hV).toLp
        (magneticHamiltonian b coupling V ψ)) ∈ magneticClosedGraph b coupling V := by
    change (hψ.memLp.toLp ψ,
      (hψ.memLp_magneticHamiltonian b coupling hV).toLp
        (magneticHamiltonian b coupling V ψ)) ∈
          (magneticClosedGraph b coupling V : Set (L2Space × L2Space))
    rw [magneticClosedGraph_eq_closure]
    exact subset_closure hg
  rw [← hA.graph_eq] at hc
  obtain ⟨u, hu, hAu⟩ := (magneticOperator b coupling V).mem_graph_iff.mp hc
  have hi := hv.inner_eq_waveInner (represents_toLp hψ.memLp)
  have h := hbound u
  rw [hu, hAu, norm_toLp_sq_eq_mass hψ.memLp, hi,
    re_inner_toLp_magneticHamiltonian_eq_magneticForm b coupling hV hψ
      hψ.memLp (hψ.memLp_magneticHamiltonian b coupling hV)] at h
  exact h

end InfiniteZero
