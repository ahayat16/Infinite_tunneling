import InfiniteZero.MagneticGraphLowerBound

/-!
# Two-projection lower bounds on the actual closed magnetic graph

A quadratic estimate with two continuous overlap terms is closed in the
graph variables. Thus an estimate on tests extends to the genuine operator
domain. The two reference vectors need not be orthogonal or normalized.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

theorem rankTwo_lower_bound_on_closure {S : Set (L2Space × L2Space)}
    (φ₁ φ₂ : L2Space) (c k E : ℝ)
    (hS : ∀ q ∈ S, c * ‖q.1‖ ^ 2 -
      k * (‖inner ℂ φ₁ q.1‖ ^ 2 + ‖inner ℂ φ₂ q.1‖ ^ 2) ≤
        (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2) :
    ∀ q ∈ closure S, c * ‖q.1‖ ^ 2 -
      k * (‖inner ℂ φ₁ q.1‖ ^ 2 + ‖inner ℂ φ₂ q.1‖ ^ 2) ≤
        (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2 := by
  have hleft : Continuous (fun q : L2Space × L2Space =>
      c * ‖q.1‖ ^ 2 -
        k * (‖inner ℂ φ₁ q.1‖ ^ 2 + ‖inner ℂ φ₂ q.1‖ ^ 2)) := by fun_prop
  have hright : Continuous (fun q : L2Space × L2Space =>
      (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2) := by fun_prop
  exact closure_minimal hS (isClosed_le hleft hright)

/-- The closed-graph inequality follows from the test inequality before any
self-adjoint realization is supplied. -/
theorem magneticClosedGraph_rankTwo_lower {b coupling c k E : ℝ}
    {V : Potential} (hV : Continuous V) {φ₁ φ₂ : Wavefunction}
    (hφ₁ : MemLp φ₁ 2 volume) (hφ₂ : MemLp φ₂ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass ψ - k * (‖waveInner φ₁ ψ‖ ^ 2 + ‖waveInner φ₂ ψ‖ ^ 2) ≤
        magneticForm b coupling V ψ - E * mass ψ) :
    ∀ q ∈ magneticClosedGraph b coupling V,
      c * ‖q.1‖ ^ 2 - k * (‖inner ℂ (hφ₁.toLp φ₁) q.1‖ ^ 2 +
        ‖inner ℂ (hφ₂.toLp φ₂) q.1‖ ^ 2) ≤
          (inner ℂ q.1 q.2).re - E * ‖q.1‖ ^ 2 := by
  intro q hq
  have hclosure : q ∈ closure (magneticTestGraph b coupling V) := by
    rwa [← magneticClosedGraph_eq_closure b coupling V]
  apply rankTwo_lower_bound_on_closure (hφ₁.toLp φ₁) (hφ₂.toLp φ₂) c k E _ q hclosure
  rintro z ⟨ψ, hψ, hψLp, hHLp, hz, hzH⟩
  rw [hz, hzH, norm_toLp_sq_eq_mass hψLp,
    inner_toLp_eq_waveInner hφ₁ hψLp, inner_toLp_eq_waveInner hφ₂ hψLp,
    re_inner_toLp_magneticHamiltonian_eq_magneticForm b coupling hV hψ hψLp hHLp]
  exact hbound ψ hψ

/-- A test inequality with two overlap terms transfers to the true domain,
without requiring orthogonality of the reference states. -/
theorem IsMagneticRealization.rankTwo_lower {b coupling c k E : ℝ}
    {V : Potential} (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {φ₁ φ₂ : Wavefunction} (hφ₁ : MemLp φ₁ 2 volume) (hφ₂ : MemLp φ₂ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass ψ - k * (‖waveInner φ₁ ψ‖ ^ 2 + ‖waveInner φ₂ ψ‖ ^ 2) ≤
        magneticForm b coupling V ψ - E * mass ψ)
    (u : (magneticOperator b coupling V).domain) :
    c * ‖(u : L2Space)‖ ^ 2 -
      k * (‖inner ℂ (hφ₁.toLp φ₁) (u : L2Space)‖ ^ 2 +
        ‖inner ℂ (hφ₂.toLp φ₂) (u : L2Space)‖ ^ 2) ≤
      (inner ℂ (u : L2Space) (magneticOperator b coupling V u)).re -
        E * ‖(u : L2Space)‖ ^ 2 := by
  apply magneticClosedGraph_rankTwo_lower hV hφ₁ hφ₂ hbound
    ((u : L2Space), magneticOperator b coupling V u)
  rw [← hA.graph_eq]
  exact LinearPMap.mem_graph _ u

/-- Orthogonality to each reference state removes both projection losses. -/
theorem IsMagneticRealization.complementTwo_lower {b coupling c k E : ℝ}
    {V : Potential} (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {φ₁ φ₂ : Wavefunction} (hφ₁ : MemLp φ₁ 2 volume) (hφ₂ : MemLp φ₂ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass ψ - k * (‖waveInner φ₁ ψ‖ ^ 2 + ‖waveInner φ₂ ψ‖ ^ 2) ≤
        magneticForm b coupling V ψ - E * mass ψ)
    (u : (magneticOperator b coupling V).domain)
    (horth₁ : inner ℂ (hφ₁.toLp φ₁) (u : L2Space) = 0)
    (horth₂ : inner ℂ (hφ₂.toLp φ₂) (u : L2Space) = 0) :
    (E + c) * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (magneticOperator b coupling V u)).re := by
  have h := hA.rankTwo_lower hV hφ₁ hφ₂ hbound u
  simp only [horth₁, horth₂, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, mul_zero, sub_zero] at h
  nlinarith only [h]

end InfiniteZero
