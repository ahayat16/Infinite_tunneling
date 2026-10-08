import InfiniteZero.L2Inversion
import InfiniteZero.MagneticTrialCovariance
import InfiniteZero.MagneticTestGraph

/-!
# The actual double-well graph is invariant under spatial inversion

Inversion first preserves the concrete test graph, by magnetic covariance.
Continuity then passes this invariance to its closure and to the realized
operator domain. No sector restriction or spectral conclusion is assumed.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

theorem l2Inversion_mem_double_magneticTestGraph
    (b coupling L : ℝ) (v : Potential) {u w : L2Space}
    (h : (u, w) ∈ magneticTestGraph b coupling (doubleWellPotential v L)) :
    (l2Inversion u, l2Inversion w) ∈
      magneticTestGraph b coupling (doubleWellPotential v L) := by
  obtain ⟨ψ, hψ, hψLp, hHLp, hu, hw⟩ := h
  change u = hψLp.toLp ψ at hu
  change w = hHLp.toLp (magneticHamiltonian b coupling (doubleWellPotential v L) ψ) at hw
  have hψinv : IsTestFunction (fun x => ψ (-x)) := hψ.inversion
  have hψinvLp : MemLp (fun x => ψ (-x)) 2 volume :=
    hψLp.comp_measurePreserving volume.measurePreserving_neg
  have hHinv : magneticHamiltonian b coupling (doubleWellPotential v L) (fun x => ψ (-x)) =
      fun x => magneticHamiltonian b coupling (doubleWellPotential v L) ψ (-x) := by
    simpa only [doubleHamiltonian] using doubleHamiltonian_inversion b L coupling v hψ.1
  have hHinvLp : MemLp
      (magneticHamiltonian b coupling (doubleWellPotential v L) (fun x => ψ (-x))) 2 volume := by
    rw [hHinv]
    exact hHLp.comp_measurePreserving volume.measurePreserving_neg
  refine ⟨fun x => ψ (-x), hψinv, hψinvLp, hHinvLp, ?_, ?_⟩
  · rw [hu]
    exact ((represents_toLp hψLp).inversion.toLp_eq hψinvLp).symm
  · rw [hw]
    have hrep : Represents (l2Inversion (hHLp.toLp _))
        (magneticHamiltonian b coupling (doubleWellPotential v L) (fun x => ψ (-x))) := by
      rw [hHinv]
      exact (represents_toLp hHLp).inversion
    exact (hrep.toLp_eq hHinvLp).symm

theorem l2Inversion_mem_double_magneticClosedGraph
    (b coupling L : ℝ) (v : Potential) {u w : L2Space}
    (h : (u, w) ∈ magneticClosedGraph b coupling (doubleWellPotential v L)) :
    (l2Inversion u, l2Inversion w) ∈
      magneticClosedGraph b coupling (doubleWellPotential v L) := by
  have hm : MapsTo (fun q : L2Space × L2Space => (l2Inversion q.1, l2Inversion q.2))
      (magneticTestGraph b coupling (doubleWellPotential v L))
      (magneticTestGraph b coupling (doubleWellPotential v L)) :=
    fun q hq => l2Inversion_mem_double_magneticTestGraph b coupling L v hq
  have hc : Continuous (fun q : L2Space × L2Space => (l2Inversion q.1, l2Inversion q.2)) :=
    (l2Inversion.continuous.comp continuous_fst).prodMk
      (l2Inversion.continuous.comp continuous_snd)
  have hcl := hm.closure hc
  change (u, w) ∈ (magneticClosedGraph b coupling (doubleWellPotential v L) : Set (L2Space × L2Space)) at h
  change (l2Inversion u, l2Inversion w) ∈
    (magneticClosedGraph b coupling (doubleWellPotential v L) : Set (L2Space × L2Space))
  rw [magneticClosedGraph_eq_closure] at h ⊢
  exact hcl h

theorem IsMagneticRealization.l2Inversion_mem_double_operator_graph
    {b coupling L : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    {u w : L2Space}
    (h : (u, w) ∈ (magneticOperator b coupling (doubleWellPotential v L)).graph) :
    (l2Inversion u, l2Inversion w) ∈
      (magneticOperator b coupling (doubleWellPotential v L)).graph := by
  rw [hA.graph_eq] at h ⊢
  exact l2Inversion_mem_double_magneticClosedGraph b coupling L v h

theorem IsMagneticRealization.exists_double_operator_inversion
    {b coupling L : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain) :
    ∃ w : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      (w : L2Space) = l2Inversion (u : L2Space) ∧
      magneticOperator b coupling (doubleWellPotential v L) w =
        l2Inversion (magneticOperator b coupling (doubleWellPotential v L) u) := by
  exact (LinearPMap.mem_graph_iff _).mp
    (hA.l2Inversion_mem_double_operator_graph
      ((magneticOperator b coupling (doubleWellPotential v L)).mem_graph u))

end InfiniteZero
