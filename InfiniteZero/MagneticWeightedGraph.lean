import InfiniteZero.MagneticGraphLowerBound
import InfiniteZero.MagneticBoundedPerturbation

/-!
# Weighted inequalities pass through the original closed test graph

Every expression below is continuous in the two graph coordinates. Thus the
weighted inequality extends without asserting that the weight preserves the
operator domain. A separate limit lemma permits smooth approximating weights.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace InfiniteZero

theorem Represents.boundedPotentialMul {u : L2Space} {ψ : Wavefunction}
    (hu : Represents u ψ) (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    Represents (boundedPotentialMul W hW hbound u) (fun x => (W x : ℂ) * ψ x) := by
  filter_upwards [coe_boundedPotentialMul W hW hbound u, hu] with x hx hux
  change (InfiniteZero.boundedPotentialMul W hW hbound u) x = (W x : ℂ) * ψ x
  rw [hx, hux]

theorem weighted_rankOne_lower_bound_on_closure {S : Set (L2Space × L2Space)}
    (M : L2Space →L[ℂ] L2Space) (φ : L2Space) (c k E : ℝ)
    (hS : ∀ q ∈ S, c * ‖M q.1‖ ^ 2 - k * ‖inner ℂ φ (M q.1)‖ ^ 2 ≤
      (inner ℂ (M q.1) (M q.2)).re - E * ‖M q.1‖ ^ 2) :
    ∀ q ∈ closure S, c * ‖M q.1‖ ^ 2 - k * ‖inner ℂ φ (M q.1)‖ ^ 2 ≤
      (inner ℂ (M q.1) (M q.2)).re - E * ‖M q.1‖ ^ 2 := by
  have hleft : Continuous (fun q : L2Space × L2Space =>
      c * ‖M q.1‖ ^ 2 - k * ‖inner ℂ φ (M q.1)‖ ^ 2) := by fun_prop
  have hright : Continuous (fun q : L2Space × L2Space =>
      (inner ℂ (M q.1) (M q.2)).re - E * ‖M q.1‖ ^ 2) := by fun_prop
  exact closure_minimal hS (isClosed_le hleft hright)

/-- A strong limit of bounded multipliers preserves a common weighted
inequality. No convergence of the derivatives of the weights is required. -/
theorem weighted_rankOne_lower_of_strong_limit
    (M : ℕ → L2Space →L[ℂ] L2Space) (N : L2Space →L[ℂ] L2Space)
    (hM : ∀ u, Tendsto (fun n => M n u) atTop (𝓝 (N u)))
    (φ u v : L2Space) (c k E : ℝ)
    (hbound : ∀ n, c * ‖M n u‖ ^ 2 - k * ‖inner ℂ φ (M n u)‖ ^ 2 ≤
      (inner ℂ (M n u) (M n v)).re - E * ‖M n u‖ ^ 2) :
    c * ‖N u‖ ^ 2 - k * ‖inner ℂ φ (N u)‖ ^ 2 ≤
      (inner ℂ (N u) (N v)).re - E * ‖N u‖ ^ 2 := by
  have hi : Tendsto (fun n => inner ℂ φ (M n u)) atTop (𝓝 (inner ℂ φ (N u))) :=
    tendsto_const_nhds.inner (hM u)
  have hip : Tendsto (fun n => inner ℂ (M n u) (M n v)) atTop
      (𝓝 (inner ℂ (N u) (N v))) := (hM u).inner (hM v)
  have hl := (((hM u).norm.pow 2).const_mul c).sub ((hi.norm.pow 2).const_mul k)
  have hr := ((Complex.continuous_re.tendsto _).comp hip).sub
    (((hM u).norm.pow 2).const_mul E)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hbound)

theorem magneticClosedGraph_weighted_rankOne_lower {b coupling c k E : ℝ}
    {V : Potential} (W : Potential) (hW : Continuous W)
    {C : ℝ} (hWbound : ∀ x, |W x| ≤ C) {φ : Wavefunction} (hφ : MemLp φ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass (fun x => (W x : ℂ) * ψ x) -
          k * ‖waveInner φ (fun x => (W x : ℂ) * ψ x)‖ ^ 2 ≤
        (waveInner (fun x => (W x : ℂ) * ψ x)
          (fun x => (W x : ℂ) * magneticHamiltonian b coupling V ψ x)).re -
          E * mass (fun x => (W x : ℂ) * ψ x)) :
    ∀ q ∈ magneticClosedGraph b coupling V,
      c * ‖boundedPotentialMul W hW hWbound q.1‖ ^ 2 -
          k * ‖inner ℂ (hφ.toLp φ) (boundedPotentialMul W hW hWbound q.1)‖ ^ 2 ≤
        (inner ℂ (boundedPotentialMul W hW hWbound q.1)
          (boundedPotentialMul W hW hWbound q.2)).re -
          E * ‖boundedPotentialMul W hW hWbound q.1‖ ^ 2 := by
  intro q hq
  have hclosure : q ∈ closure (magneticTestGraph b coupling V) := by
    rwa [← magneticClosedGraph_eq_closure b coupling V]
  apply weighted_rankOne_lower_bound_on_closure
    (boundedPotentialMul W hW hWbound) (hφ.toLp φ) c k E _ q hclosure
  rintro z ⟨ψ, hψ, hψLp, hHLp, hz, hzH⟩
  rw [hz, hzH]
  have hu := (represents_toLp hψLp).boundedPotentialMul W hW hWbound
  have hv := (represents_toLp hHLp).boundedPotentialMul W hW hWbound
  rw [hu.norm_sq_eq_mass, (represents_toLp hφ).inner_eq_waveInner hu,
    hu.inner_eq_waveInner hv]
  exact hbound ψ hψ

/-- The weight is only a bounded multiplier here; it need not preserve the
domain of the second-order operator. -/
theorem IsMagneticRealization.weighted_rankOne_lower {b coupling c k E : ℝ}
    {V : Potential} (hA : IsMagneticRealization b coupling V)
    (W : Potential) (hW : Continuous W) {C : ℝ} (hWbound : ∀ x, |W x| ≤ C)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass (fun x => (W x : ℂ) * ψ x) -
          k * ‖waveInner φ (fun x => (W x : ℂ) * ψ x)‖ ^ 2 ≤
        (waveInner (fun x => (W x : ℂ) * ψ x)
          (fun x => (W x : ℂ) * magneticHamiltonian b coupling V ψ x)).re -
          E * mass (fun x => (W x : ℂ) * ψ x))
    (u : (magneticOperator b coupling V).domain) :
    c * ‖boundedPotentialMul W hW hWbound (u : L2Space)‖ ^ 2 -
        k * ‖inner ℂ (hφ.toLp φ) (boundedPotentialMul W hW hWbound (u : L2Space))‖ ^ 2 ≤
      (inner ℂ (boundedPotentialMul W hW hWbound (u : L2Space))
        (boundedPotentialMul W hW hWbound (magneticOperator b coupling V u))).re -
        E * ‖boundedPotentialMul W hW hWbound (u : L2Space)‖ ^ 2 := by
  apply magneticClosedGraph_weighted_rankOne_lower W hW hWbound hφ hbound
    ((u : L2Space), magneticOperator b coupling V u)
  rw [← hA.graph_eq]
  exact LinearPMap.mem_graph _ u

end InfiniteZero
