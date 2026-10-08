import InfiniteZero.MagneticTestGraph
import InfiniteZero.MagneticIntegrationByPartsLocal
import InfiniteZero.WavefunctionL2Bridge

/-!
# Smooth inhomogeneous solutions belong to the closed operator domain

A smooth `L²` function whose magnetic Hamiltonian also belongs to `L²`
lies in the domain of the prescribed closed magnetic operator. Integration
by parts against compactly supported tests gives the adjoint identity;
continuity extends it to the closed test graph, and self-adjointness
identifies the adjoint domain with the original domain.

The realization certificate is an explicit hypothesis. This argument
uses neither a new regularity theorem nor the eigenfunction correspondence
contained in that certificate.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace InfiniteZero

/-- The magnetic Hamiltonian is symmetric when tested against a compactly
supported smooth function, even if the other smooth function has no global
energy bound. -/
theorem waveInner_magneticHamiltonian_smooth_right (b coupling : ℝ)
    {V : Potential} {ψ φ : Wavefunction} (hV : Continuous V)
    (hψ : IsTestFunction ψ) (hφ : ContDiff ℝ ∞ φ) :
    waveInner ψ (magneticHamiltonian b coupling V φ) =
      waveInner (magneticHamiltonian b coupling V ψ) φ := by
  have hkin (i : Fin 2) := hψ.integrable_star_mul
    (contDiff_covariantDerivative b coupling i
      (contDiff_covariantDerivative b coupling i hφ)).continuous
  have hkin' (i : Fin 2) :=
    ((hψ.covariantDerivative b coupling i).covariantDerivative b coupling i).integrable_star_mul
      hφ.continuous
  have hpot : Integrable (fun x => star (ψ x) *
      (((coupling ^ 2 * V x : ℝ) : ℂ) * φ x)) := hψ.integrable_star_mul
    ((Complex.continuous_ofReal.comp (continuous_const.mul hV)).mul hφ.continuous)
  have hp (x : Plane) :
      star (((coupling ^ 2 * V x : ℝ) : ℂ) * ψ x) * φ x =
        star (ψ x) * (((coupling ^ 2 * V x : ℝ) : ℂ) * φ x) := by
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  unfold waveInner magneticHamiltonian
  simp_rw [mul_add, Finset.mul_sum, star_add, star_sum, add_mul, Finset.sum_mul, hp]
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hkin i)) hpot,
    integral_add (integrable_finsetSum Finset.univ (fun i _ => hkin' i)) hpot,
    integral_finsetSum Finset.univ (fun i _ => hkin i),
    integral_finsetSum Finset.univ (fun i _ => hkin' i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change waveInner ψ (covariantDerivative b coupling i (covariantDerivative b coupling i φ)) =
    waveInner (covariantDerivative b coupling i (covariantDerivative b coupling i ψ)) φ
  rw [waveInner_covariantDerivative_smooth_right b coupling i hψ
      (contDiff_covariantDerivative b coupling i hφ),
    waveInner_covariantDerivative_smooth_right b coupling i
      (hψ.covariantDerivative b coupling i) hφ]

/-- The distributional adjoint identity extends from the concrete test
functions to their prescribed closed graph. -/
theorem magneticClosedGraph_inner_of_smooth {b coupling : ℝ} {V : Potential}
    (hV : Continuous V) {ψ : Wavefunction} (hψ : ContDiff ℝ ∞ ψ)
    {u g : L2Space} (hu : Represents u ψ)
    (hg : Represents g (magneticHamiltonian b coupling V ψ)) :
    ∀ z ∈ magneticClosedGraph b coupling V,
      inner ℂ z.2 u = inner ℂ z.1 g := by
  have htest : ∀ z ∈ magneticTestGraph b coupling V,
      inner ℂ z.2 u = inner ℂ z.1 g := by
    rintro z ⟨φ, hφ, hφL, hHL, hz, hzH⟩
    rw [hzH, hz, (represents_toLp hHL).inner_eq_waveInner hu,
      (represents_toLp hφL).inner_eq_waveInner hg]
    exact (waveInner_magneticHamiltonian_smooth_right b coupling hV hφ hψ).symm
  have hclosed : IsClosed {z : L2Space × L2Space |
      inner ℂ z.2 u = inner ℂ z.1 g} := isClosed_eq (by fun_prop) (by fun_prop)
  intro z hz
  apply closure_minimal htest hclosed
  rwa [← magneticClosedGraph_eq_closure b coupling V]

/-- A smooth `L²` solution with `L²` Hamiltonian belongs to the genuine
closed operator graph. Only graph identification and self-adjointness of
the supplied realization are used. -/
theorem IsMagneticRealization.mem_graph_of_smooth {b coupling : ℝ} {V : Potential}
    (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {ψ : Wavefunction} (hψ : ContDiff ℝ ∞ ψ) {u g : L2Space}
    (hu : Represents u ψ) (hg : Represents g (magneticHamiltonian b coupling V ψ)) :
    (u, g) ∈ (magneticOperator b coupling V).graph := by
  have hstar : (magneticOperator b coupling V).adjoint = magneticOperator b coupling V :=
    LinearPMap.isSelfAdjoint_def.mp hA.selfAdjoint
  rw [← hstar, LinearPMap.adjoint_graph_eq_graph_adjoint hA.dense_domain,
    Submodule.mem_adjoint_iff]
  intro v w hvw
  rw [hA.graph_eq] at hvw
  exact sub_eq_zero.mpr (magneticClosedGraph_inner_of_smooth hV hψ hu hg (v, w) hvw)

/-- Explicit `MemLp` witnesses give a point of the closed graph without
choosing separate Hilbert-space representatives. -/
theorem IsMagneticRealization.mem_graph_toLp_of_smooth {b coupling : ℝ} {V : Potential}
    (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {ψ : Wavefunction} (hψ : ContDiff ℝ ∞ ψ)
    (hψL : MemLp ψ 2 volume)
    (hH : MemLp (magneticHamiltonian b coupling V ψ) 2 volume) :
    (hψL.toLp ψ, hH.toLp (magneticHamiltonian b coupling V ψ)) ∈
      (magneticOperator b coupling V).graph :=
  hA.mem_graph_of_smooth hV hψ (represents_toLp hψL) (represents_toLp hH)

end InfiniteZero
