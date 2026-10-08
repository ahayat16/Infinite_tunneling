import InfiniteZero.L2ParitySectors
import InfiniteZero.DoubleWellInversionGraph

/-!
# Parity projections preserve the actual double-well graph

The closed operator graph is a complex subspace invariant under spatial
inversion. It is therefore preserved by both `(I + J)/2` and `(I - J)/2`.
The final statement uses the orthogonal projections of the closed parity
sectors, in the form needed for a reducing-subspace restriction.
-/

noncomputable section

namespace InfiniteZero

theorem IsMagneticRealization.l2ParityProjection_mem_double_operator_graph
    {b coupling L : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) {u w : L2Space}
    (h : (u, w) ∈ (magneticOperator b coupling (doubleWellPotential v L)).graph) :
    (l2ParityProjection even u, l2ParityProjection even w) ∈
      (magneticOperator b coupling (doubleWellPotential v L)).graph := by
  let G := (magneticOperator b coupling (doubleWellPotential v L)).graph
  have hJ := hA.l2Inversion_mem_double_operator_graph h
  rw [l2ParityProjection_apply, l2ParityProjection_apply]
  cases even
  · exact G.smul_mem (1 / 2 : ℂ) (G.add_mem h (G.neg_mem hJ))
  · exact G.smul_mem (1 / 2 : ℂ) (G.add_mem h hJ)

theorem IsMagneticRealization.parityStarProjection_double_graph
    {b coupling L : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) :
    ∀ q ∈ (magneticOperator b coupling (doubleWellPotential v L)).graph,
      ((l2ParitySector even).starProjection q.1, (l2ParitySector even).starProjection q.2) ∈
        (magneticOperator b coupling (doubleWellPotential v L)).graph := by
  intro q hq
  rw [← l2ParityProjection_eq_starProjection]
  exact hA.l2ParityProjection_mem_double_operator_graph even hq

end InfiniteZero
