import InfiniteZero.MagneticTestGraph
import InfiniteZero.WavefunctionL2Bridge

/-!
# Lower energy bounds on the actual closed operator

A rank-one quadratic lower bound is a closed condition on a pair `(u, Hu)`
in physical L². Consequently an estimate on every test function extends to
the closed test graph. No density assertion for orthogonal test functions
and no additional spectral or form-domain theorem is assumed.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

theorem rankOne_lower_bound_on_closure {S : Set (L2Space × L2Space)}
    (φ : L2Space) (c k E : ℝ)
    (hS : ∀ q ∈ S, c * ‖q.1‖ ^ 2 - k * ‖inner ℂ φ q.1‖ ^ 2 ≤
      (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2) :
    ∀ q ∈ closure S, c * ‖q.1‖ ^ 2 - k * ‖inner ℂ φ q.1‖ ^ 2 ≤
      (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2 := by
  have hleft : Continuous (fun q : L2Space × L2Space =>
      c * ‖q.1‖ ^ 2 - k * ‖inner ℂ φ q.1‖ ^ 2) := by fun_prop
  have hright : Continuous (fun q : L2Space × L2Space =>
      (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2) := by fun_prop
  exact closure_minimal hS (isClosed_le hleft hright)

/-- The L² inequality holds on the specified closed graph, independently of
whether it has yet been identified with a self-adjoint operator. -/
theorem magneticClosedGraph_rankOne_lower {b coupling c k E : ℝ}
    {V : Potential} (hV : Continuous V) {φ : Wavefunction} (hφ : MemLp φ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass ψ - k * ‖waveInner φ ψ‖ ^ 2 ≤
        magneticForm b coupling V ψ - E * mass ψ) :
    ∀ q ∈ magneticClosedGraph b coupling V,
      c * ‖q.1‖ ^ 2 - k * ‖inner ℂ (hφ.toLp φ) q.1‖ ^ 2 ≤
        (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2 := by
  intro q hq
  have hclosure : q ∈ closure (magneticTestGraph b coupling V) := by
    rwa [← magneticClosedGraph_eq_closure b coupling V]
  apply rankOne_lower_bound_on_closure (hφ.toLp φ) c k E _ q hclosure
  rintro z ⟨ψ, hψ, hψLp, hHLp, hz, hzH⟩
  rw [hz, hzH, norm_toLp_sq_eq_mass hψLp, inner_toLp_eq_waveInner hφ hψLp,
    re_inner_toLp_magneticHamiltonian_eq_magneticForm b coupling hV hψ hψLp hHLp]
  exact hbound ψ hψ

/-- A proved test-function estimate transfers to the genuine operator domain
using only its explicit graph-realization certificate. -/
theorem IsMagneticRealization.rankOne_lower {b coupling c k E : ℝ}
    {V : Potential} (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass ψ - k * ‖waveInner φ ψ‖ ^ 2 ≤
        magneticForm b coupling V ψ - E * mass ψ)
    (u : (magneticOperator b coupling V).domain) :
    c * ‖(u : L2Space)‖ ^ 2 - k * ‖inner ℂ (hφ.toLp φ) (u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (magneticOperator b coupling V u)).re -
        E * ‖(u : L2Space)‖ ^ 2 := by
  apply magneticClosedGraph_rankOne_lower hV hφ hbound
    ((u : L2Space), magneticOperator b coupling V u)
  rw [← hA.graph_eq]
  exact LinearPMap.mem_graph _ u

theorem IsMagneticRealization.complement_lower {b coupling c k E : ℝ}
    {V : Potential} (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass ψ - k * ‖waveInner φ ψ‖ ^ 2 ≤
        magneticForm b coupling V ψ - E * mass ψ)
    (u : (magneticOperator b coupling V).domain)
    (horth : inner ℂ (hφ.toLp φ) (u : L2Space) = 0) :
    (E + c) * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (magneticOperator b coupling V u)).re := by
  have h := hA.rankOne_lower hV hφ hbound u
  simp only [horth, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero] at h
  nlinarith only [h]

end InfiniteZero
