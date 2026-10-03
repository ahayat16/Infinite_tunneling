import InfiniteZero.DoubleWellParityGraph
import InfiniteZero.MagneticGraphLowerBound

/-!
# Parity test bounds extend to the actual parity domain

Projecting the test graph by `(I ± J)/2` produces genuine tests of that
parity. Its quadratic lower bounds are closed in graph norm. This supplies
the parity analogue of the full-space test-to-operator bridge, without
assuming that arbitrary graph approximants already have the right parity.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

theorem Represents.hasParity_of_continuous {u : L2Space} {ψ : Wavefunction}
    (hu : Represents u ψ) (hψ : Continuous ψ) {even : Bool}
    (hp : HasL2Parity even u) : HasParity even ψ := by
  have hneg := volume.measurePreserving_neg.quasiMeasurePreserving.ae hu
  have hae : (fun x => ψ (-x)) =ᵐ[volume] (fun x => if even then ψ x else -ψ x) := by
    filter_upwards [hu, hneg, hp] with x hx hnx hpx
    simpa only [hx, hnx] using hpx
  have heq := Measure.eq_of_ae_eq hae (hψ.comp continuous_neg)
    (by cases even; exact hψ.neg; exact hψ)
  exact congrFun heq

theorem l2ParityProjection_mem_double_magneticTestGraph
    (b coupling L : ℝ) (v : Potential) (even : Bool) {u w : L2Space}
    (h : (u, w) ∈ magneticTestGraph b coupling (doubleWellPotential v L)) :
    (l2ParityProjection even u, l2ParityProjection even w) ∈
      magneticTestGraph b coupling (doubleWellPotential v L) := by
  let G := magneticTestGraphSubmodule b coupling (doubleWellPotential v L)
  have hJ := l2Inversion_mem_double_magneticTestGraph b coupling L v h
  rw [l2ParityProjection_apply, l2ParityProjection_apply]
  cases even
  · exact G.smul_mem (1 / 2 : ℂ) (G.add_mem h (G.neg_mem hJ))
  · exact G.smul_mem (1 / 2 : ℂ) (G.add_mem h hJ)

theorem magneticClosedGraph_parity_lower {b coupling L E : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L)) (even : Bool)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ → HasParity even ψ →
      E * mass ψ ≤ magneticForm b coupling (doubleWellPotential v L) ψ)
    {u w : L2Space} (hgraph : (u, w) ∈ magneticClosedGraph b coupling (doubleWellPotential v L))
    (hu : HasL2Parity even u) : E * ‖u‖ ^ 2 ≤ (inner ℂ u w).re := by
  let P := l2ParityProjection even
  have htest : ∀ q ∈ magneticTestGraph b coupling (doubleWellPotential v L),
      E * ‖P q.1‖ ^ 2 ≤ (inner ℂ (P q.1) (P q.2)).re := by
    intro q hq
    obtain ⟨ψ, hψ, hψLp, hHLp, hz, hzH⟩ :=
      l2ParityProjection_mem_double_magneticTestGraph b coupling L v even hq
    dsimp only [Prod.fst, Prod.snd] at hz hzH
    have hrep : Represents (P q.1) ψ := by
      change Represents (l2ParityProjection even q.1) ψ
      rw [hz]
      exact represents_toLp hψLp
    have hpar := hrep.hasParity_of_continuous hψ.1.continuous
      ((mem_l2ParitySector_iff even _).mp (l2ParityProjection_mem even q.1))
    change E * ‖l2ParityProjection even q.1‖ ^ 2 ≤
      (inner ℂ (l2ParityProjection even q.1) (l2ParityProjection even q.2)).re
    rw [hz, hzH, norm_toLp_sq_eq_mass hψLp,
      re_inner_toLp_magneticHamiltonian_eq_magneticForm b coupling hV hψ hψLp hHLp]
    exact hbound ψ hψ hpar
  have hleft : Continuous (fun q : L2Space × L2Space => E * ‖P q.1‖ ^ 2) :=
    continuous_const.mul ((P.continuous.comp continuous_fst).norm.pow 2)
  have hright : Continuous (fun q : L2Space × L2Space =>
      (inner ℂ (P q.1) (P q.2)).re) :=
    Complex.continuous_re.comp ((P.continuous.comp continuous_fst).inner
      (P.continuous.comp continuous_snd))
  have hclosure : ∀ q ∈ closure (magneticTestGraph b coupling (doubleWellPotential v L)),
      E * ‖P q.1‖ ^ 2 ≤ (inner ℂ (P q.1) (P q.2)).re :=
    closure_minimal htest (isClosed_le hleft hright)
  have hc : (u, w) ∈ closure (magneticTestGraph b coupling (doubleWellPotential v L)) := by
    change (u, w) ∈ (magneticClosedGraph b coupling (doubleWellPotential v L) :
      Set (L2Space × L2Space)) at hgraph
    rwa [magneticClosedGraph_eq_closure] at hgraph
  have h := hclosure (u, w) hc
  have hPu : P u = u :=
    l2ParityProjection_eq_self ((mem_l2ParitySector_iff even u).mpr hu)
  have hi : inner ℂ u (P w) = inner ℂ u w := by
    rw [show P = (l2ParitySector even).starProjection from
      l2ParityProjection_eq_starProjection even,
      ← Submodule.inner_starProjection_left_eq_right]
    rw [← l2ParityProjection_eq_starProjection, hPu]
  simpa only [Prod.fst, Prod.snd, hPu, hi] using h

theorem IsMagneticRealization.parity_lower_of_test
    {b coupling L E : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) (even : Bool)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ → HasParity even ψ →
      E * mass ψ ≤ magneticForm b coupling (doubleWellPotential v L) ψ)
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : HasL2Parity even (u : L2Space)) :
    E * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space)
        (magneticOperator b coupling (doubleWellPotential v L) u)).re := by
  apply magneticClosedGraph_parity_lower hV even hbound _ hu
  rw [← hA.graph_eq]
  exact LinearPMap.mem_graph _ u

end InfiniteZero
