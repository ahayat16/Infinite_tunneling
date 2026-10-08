import InfiniteZero.MagneticBoundedPerturbation
import InfiniteZero.ConstructionSmooth

/-!
# The constructed atomic potential and the radial core have the same domain

The actual difference between the constructed potential and its radial core
is bounded and continuous. Consequently their canonical operators have the
same domain. Realization certificates are needed only to identify operator
values with the points of the concrete closed graphs.
-/

noncomputable section
open Set
namespace InfiniteZero.CuspParameters

/-- The actual perturbation of the radial core by the two cusp components. -/
def atomicPerturbation (p : CuspParameters) : Potential := p.potential - p.core

theorem atomicPerturbation_continuous {p : CuspParameters} (hp : p.BasicConditions) :
    Continuous p.atomicPerturbation :=
  (potential_contDiff hp).continuous.sub (core_contDiff hp.r₀_pos).continuous

/-- Both original potentials lie in `[-1,0]`, hence their difference is bounded. -/
theorem abs_atomicPerturbation_le_two {p : CuspParameters} (hp : p.BasicConditions)
    (x : Plane) : |p.atomicPerturbation x| ≤ 2 := by
  have hc := p.core_range x
  have hpv := potential_range hp x
  change |p.potential x - p.core x| ≤ 2
  exact abs_le.mpr ⟨by linarith [hc.1, hc.2, hpv.1, hpv.2],
    by linarith [hc.1, hc.2, hpv.1, hpv.2]⟩

@[simp] theorem core_add_atomicPerturbation (p : CuspParameters) :
    p.core + p.atomicPerturbation = p.potential := by
  ext x
  simp only [atomicPerturbation, Pi.add_apply, Pi.sub_apply]
  ring

/-- Multiplication by the actual cusp perturbation on physical complex L². -/
def atomicPerturbationMul {p : CuspParameters} (hp : p.BasicConditions) :
    L2Space →L[ℂ] L2Space :=
  boundedPotentialMul p.atomicPerturbation (atomicPerturbation_continuous hp)
    (abs_atomicPerturbation_le_two hp)

theorem coe_atomicPerturbationMul {p : CuspParameters} (hp : p.BasicConditions)
    (u : L2Space) :
    atomicPerturbationMul hp u =ᵐ[MeasureTheory.volume]
      fun x => ((p.potential x - p.core x : ℝ) : ℂ) * u x :=
  coe_boundedPotentialMul p.atomicPerturbation (atomicPerturbation_continuous hp)
    (abs_atomicPerturbation_le_two hp) u

theorem norm_atomicPerturbationMul_apply_le {p : CuspParameters} (hp : p.BasicConditions)
    (u : L2Space) : ‖atomicPerturbationMul hp u‖ ≤ 2 * ‖u‖ :=
  norm_boundedPotentialMul_apply_le p.atomicPerturbation (atomicPerturbation_continuous hp)
    (abs_atomicPerturbation_le_two hp) u

/-- Exact transport of the concrete closed graphs by the cusp perturbation. -/
theorem atomicGraphShear_mem_closedGraph_iff {p : CuspParameters} (hp : p.BasicConditions)
    (coupling : ℝ) (q : L2Space × L2Space) :
    magneticGraphShear coupling (atomicPerturbationMul hp) q ∈
        magneticClosedGraph p.b coupling p.potential ↔
      q ∈ magneticClosedGraph p.b coupling p.core := by
  simpa only [core_add_atomicPerturbation, atomicPerturbationMul] using
    magneticGraphShear_mem_closedGraph_iff p.b coupling p.core p.atomicPerturbation
      (atomicPerturbation_continuous hp) (abs_atomicPerturbation_le_two hp) q

/-- Equality of domains uses no realization certificate or spectral hypothesis. -/
theorem atomicOperator_domain_eq_core {p : CuspParameters} (hp : p.BasicConditions)
    (coupling : ℝ) :
    (magneticOperator p.b coupling p.potential).domain =
      (magneticOperator p.b coupling p.core).domain := by
  simpa only [core_add_atomicPerturbation] using
    magneticOperator_domain_add_potential p.b coupling p.core p.atomicPerturbation
      (atomicPerturbation_continuous hp) (abs_atomicPerturbation_le_two hp)

/-- The same transport for operator graphs after their standard identification
with the canonical closed test graphs. -/
theorem atomicGraphShear_mem_graph_iff {p : CuspParameters} (hp : p.BasicConditions)
    (coupling : ℝ) (hAcore : IsMagneticRealization p.b coupling p.core)
    (hApot : IsMagneticRealization p.b coupling p.potential) (q : L2Space × L2Space) :
    magneticGraphShear coupling (atomicPerturbationMul hp) q ∈
        (magneticOperator p.b coupling p.potential).graph ↔
      q ∈ (magneticOperator p.b coupling p.core).graph := by
  rw [hAcore.graph_eq, hApot.graph_eq]
  exact atomicGraphShear_mem_closedGraph_iff hp coupling q

/-- The full operator acts on every core-domain vector by the expected bounded correction. -/
theorem atomicOperator_graph_of_core {p : CuspParameters} (hp : p.BasicConditions)
    (coupling : ℝ) (hAcore : IsMagneticRealization p.b coupling p.core)
    (hApot : IsMagneticRealization p.b coupling p.potential)
    (u : (magneticOperator p.b coupling p.core).domain) :
    ((u : L2Space), magneticOperator p.b coupling p.core u +
        (coupling ^ 2 : ℂ) • atomicPerturbationMul hp u) ∈
      (magneticOperator p.b coupling p.potential).graph :=
  (atomicGraphShear_mem_graph_iff hp coupling hAcore hApot _).mpr
    (LinearPMap.mem_graph _ u)

/-- In particular, a radial-core eigenvector is in the full graph with its exact residual. -/
theorem atomicOperator_graph_of_core_eigenvector {p : CuspParameters} (hp : p.BasicConditions)
    (coupling : ℝ) (hAcore : IsMagneticRealization p.b coupling p.core)
    (hApot : IsMagneticRealization p.b coupling p.potential) {E : ℝ} {u : L2Space}
    (hu : u ∈ operatorEigenspace (magneticOperator p.b coupling p.core) E) :
    (u, (E : ℂ) • u + (coupling ^ 2 : ℂ) • atomicPerturbationMul hp u) ∈
      (magneticOperator p.b coupling p.potential).graph :=
  (atomicGraphShear_mem_graph_iff hp coupling hAcore hApot _).mpr hu

end InfiniteZero.CuspParameters
