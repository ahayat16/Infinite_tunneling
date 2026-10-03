import InfiniteZero.MagneticModel
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The genuine unbounded operator on physical L²

The magnetic operator is defined by closing the span of its explicit test-function
graph. `IsMagneticRealization` states the standard analytic obligations connecting
that graph to the self-adjoint operator and the classical differential model.
It contains no tunneling, spectral isolation, multiplicity, or crossing assumption.
No declaration in this file is admitted.

For the connection to the manuscript, `magneticOperator b coupling v` realizes
`h_v(λ)` in TeX `eq:one-well-unscaled`, and inserting `doubleWellPotential v L`
realizes `H_v(λ)` in `eq:double-well-unscaled`, with `λ = coupling`. These are
the unscaled operators on complex `L²(ℝ²)`. The final `OperatorMainConclusion`
combines this classical connection with the constructed ground eigenvectors,
multiplicities, and positive gaps required by `thm:main`.

The theorem `magnetic_realization` in `Remaining.lean` supplies this file's
realization certificate as the explicitly recorded admission A002, for smooth
bounded real potentials. Its references, natural-language proof, and precise
scope are in `docs/CLASSICAL_OPERATOR_REALIZATION.md`. A002 does not supply
the special potential's atomic gap or any tunneling estimate.
-/

noncomputable section

open MeasureTheory Set

namespace InfiniteZero

/-- Physical complex `L²(ℝ², dx)`: functions are identified when equal almost
everywhere for planar Lebesgue measure. In contrast, `Wavefunction` consists
of pointwise functions before this identification. -/
abbrev L2Space := MeasureTheory.Lp ℂ 2 (volume : Measure Plane)

/-- The `L²` class `u` agrees almost everywhere with the pointwise function
`ψ`. In particular, a smooth eigenfunction may represent an operator
eigenvector without being definitionally equal to the class's chosen
measurable representative. -/
def Represents (u : L2Space) (ψ : Wavefunction) : Prop :=
  (u : Plane → ℂ) =ᵐ[volume] ψ

/-- The actual graph of the magnetic differential expression on smooth,
compactly supported functions, embedded in `L² × L²`: pairs `([ψ],[Hψ])`.
The explicit `MemLp` witnesses ensure both entries really are `L²` classes;
no arbitrary graph or operator is supplied as an input. -/
def magneticTestGraph (b coupling : ℝ) (V : Potential) : Set (L2Space × L2Space) :=
  {q | ∃ ψ : Wavefunction, IsTestFunction ψ ∧
    ∃ hψ : MemLp ψ 2 volume, ∃ hH : MemLp (magneticHamiltonian b coupling V ψ) 2 volume,
      q.1 = hψ.toLp ψ ∧ q.2 = hH.toLp (magneticHamiltonian b coupling V ψ)}

/-- The closed complex linear span of the concrete test graph in
`L² × L²`. For the smooth bounded real potentials used here, the realization
certificate identifies it with the graph of the closed self-adjoint
Hamiltonian. The span and closure are explicit, so the domain is fixed by
the test-function differential expression. -/
def magneticClosedGraph (b coupling : ℝ) (V : Potential) :
    Submodule ℂ (L2Space × L2Space) :=
  (Submodule.span ℂ (magneticTestGraph b coupling V)).topologicalClosure

/-- The canonical partial linear map extracted from `magneticClosedGraph`.
Its domain is a complex submodule of physical `L²`, as required for an
unbounded Hamiltonian. Extraction from a submodule of `L² × L²` alone does
not certify that it is the intended single-valued graph: the `graph_eq` field
of `IsMagneticRealization` proves precisely that identification, and
`selfAdjoint` provides the actual self-adjointness assertion.
With `V = v` or `doubleWellPotential v L`, this realizes the respective
unscaled Hamiltonians in TeX `eq:one-well-unscaled` and
`eq:double-well-unscaled`. -/
def magneticOperator (b coupling : ℝ) (V : Potential) : L2Space →ₗ.[ℂ] L2Space :=
  (magneticClosedGraph b coupling V).toLinearPMap

/-- The full complex operator eigenspace at real energy `E`:
`{u ∈ Dom(A) | Au = E u}`, including zero. The graph formulation encodes
membership in the unbounded operator domain as well as the equation.
This definition does not presume that `E` is an eigenvalue, is lowest,
or is isolated. -/
def operatorEigenspace (A : L2Space →ₗ.[ℂ] L2Space) (E : ℝ) : Submodule ℂ L2Space :=
  A.graph.comap ((LinearMap.id : L2Space →ₗ[ℂ] L2Space).prod
    ((E : ℂ) • (LinearMap.id : L2Space →ₗ[ℂ] L2Space)))

@[simp] theorem mem_operatorEigenspace (A : L2Space →ₗ.[ℂ] L2Space) (E : ℝ)
    (u : L2Space) : u ∈ operatorEigenspace A E ↔ (u, (E : ℂ) • u) ∈ A.graph := Iff.rfl

/-- The infimum of `Re ⟨u,Au⟩` over unit vectors in the actual operator
domain. The `bottom_eq` field below identifies it with the test-function
infimum `variationalBottom`; neither infimum definition by itself asserts
that a normalized ground eigenvector exists. -/
def operatorVariationalBottom (A : L2Space →ₗ.[ℂ] L2Space) : ℝ :=
  sInf {E | ∃ u : A.domain, ‖(u : L2Space)‖ = 1 ∧
    (inner ℂ (u : L2Space) (A u)).re = E}

/-- Inversion parity of an `L²` class, interpreted almost everywhere:
`true` means `u(-x) = u(x)` and `false` means `u(-x) = -u(x)`.
This is the operator-space version of `HasParity` and of the even/odd
sectors in TeX §`sec:introduction`. -/
def HasL2Parity (even : Bool) (u : L2Space) : Prop :=
  ∀ᵐ x : Plane, u (-x) = if even then u x else -u x

/-- A coercive gap inequality on the orthogonal complement of the entire
eigenspace at `E`: some `δ > 0` satisfies
`Re ⟨u,Au⟩ ≥ (E+δ) ‖u‖²` for every domain vector orthogonal to that space.
The quantifiers keep `δ` fixed before `u`; in the final theorem it may
depend on the fixed operator, hence on the coupling and separation.

Combined with self-adjointness, the global lower bound at `E`, and a
nonzero finite-dimensional eigenspace there, this expresses that the ground
level is isolated. A dimension assertion alone does not supply this gap.
`OperatorMainConclusion` includes all these companion facts to interpret
the lowest-level crossings in TeX `thm:main(i)`. This inequality is proved
by the special-potential spectral analysis; it is not part of A002. -/
def HasGapAboveGround (A : L2Space →ₗ.[ℂ] L2Space) (E : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ u : A.domain,
    (∀ w ∈ operatorEigenspace A E, inner ℂ w (u : L2Space) = 0) →
      (E + δ) * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re

theorem Represents.hasL2Parity {u : L2Space} {ψ : Wavefunction} {even : Bool}
    (hu : Represents u ψ) (hψ : HasParity even ψ) : HasL2Parity even u := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure Plane)).quasiMeasurePreserving.ae hu
  filter_upwards [hu, hneg] with x hx hnx
  rw [hnx, hx]
  exact hψ x

theorem Represents.ne_zero_of_mass_one {u : L2Space} {ψ : Wavefunction}
    (hu : Represents u ψ) (hψ : mass ψ = 1) : u ≠ 0 := by
  intro hz
  have hzero : ψ =ᵐ[volume] (0 : Wavefunction) := by
    exact hu.symm.trans (hz ▸ Lp.coeFn_zero ℂ 2 volume)
  have hm : mass ψ = 0 := by
    unfold mass
    calc
      (∫ x : Plane, ‖ψ x‖ ^ 2) = ∫ _x : Plane, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hzero] with x hx
        simp [hx]
      _ = 0 := integral_zero _ _
  linarith

/-- The classical connection between the explicitly closed test graph, its
self-adjoint `L²` operator, the test-function variational bottom, and smooth
classical eigenspaces. The certificate itself has no smoothness or boundedness
arguments; the admitted theorem `magnetic_realization` proves its existence
for every smooth bounded real `V` and every real `b, coupling` (A002).
See `docs/CLASSICAL_OPERATOR_REALIZATION.md` for the classical references
and a natural-language proof of each field.

For a reviewer of TeX `thm:main`, these fields justify using the differential
and variational definitions to discuss the genuine unbounded Hamiltonian.
They contain no assertion that an eigenvalue exists, no atomic or double-well
gap, no dimension or parity claim, and no source or tunneling estimate. Those
properties are constructed in the subsequent proof. -/
structure IsMagneticRealization (b coupling : ℝ) (V : Potential) : Prop where
  /-- The partial operator's graph is exactly the prescribed closed test
  graph; extraction has not changed the graph being realized. -/
  graph_eq : (magneticOperator b coupling V).graph = magneticClosedGraph b coupling V
  /-- Self-adjointness in Mathlib's unbounded `LinearPMap` sense. In
  particular, the operator domain is dense, as `dense_domain` below proves. -/
  selfAdjoint : IsSelfAdjoint (magneticOperator b coupling V)
  /-- Closing the test operator does not change the Rayleigh infimum. -/
  bottom_eq : operatorVariationalBottom (magneticOperator b coupling V) =
    variationalBottom b coupling V
  /-- The test-function variational bottom bounds the quadratic energy of
  every vector in the closed operator domain, including noncompact vectors. -/
  lower_bound : ∀ u : (magneticOperator b coupling V).domain,
    variationalBottom b coupling V * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (magneticOperator b coupling V u)).re
  /-- At each real energy, an `L²` operator eigenvector has a smooth
  square-integrable pointwise solution as representative, and conversely.
  This includes the classical local elliptic-regularity/domain connection. -/
  eigenfunction_iff : ∀ (E : ℝ) (u : L2Space),
    u ∈ operatorEigenspace (magneticOperator b coupling V) E ↔
      ∃ ψ : Wavefunction, IsEigenfunction b coupling V E ψ ∧ Represents u ψ
  /-- Passage from smooth representatives to `L²` classes gives a complex
  linear equivalence of the full eigenspaces, preserving representatives.
  It therefore transfers dimensions, rather than identifying only a chosen
  family of test modes with part of the operator eigenspace. -/
  eigenspace_equiv : ∀ (E : ℝ) (G : Submodule ℂ Wavefunction),
    (∀ ψ, ψ ∈ G ↔ IsEigenfunction b coupling V E ψ) →
    ∃ e : G ≃ₗ[ℂ] operatorEigenspace (magneticOperator b coupling V) E,
      ∀ ψ : G, Represents (e ψ : L2Space) (ψ : Wavefunction)

/-- Density follows from mathlib's genuine self-adjointness predicate; its
adjoint's fallback definition cannot give a spurious non-dense fixed point. -/
theorem IsMagneticRealization.dense_domain {b coupling : ℝ} {V : Potential}
    (h : IsMagneticRealization b coupling V) :
    Dense ((magneticOperator b coupling V).domain : Set L2Space) :=
  h.selfAdjoint.dense_domain

theorem IsMagneticRealization.eigenspace_finrank {b coupling : ℝ} {V : Potential}
    (h : IsMagneticRealization b coupling V) (E : ℝ) (G : Submodule ℂ Wavefunction)
    (hG : ∀ ψ, ψ ∈ G ↔ IsEigenfunction b coupling V E ψ) :
    Module.finrank ℂ (operatorEigenspace (magneticOperator b coupling V) E) =
      Module.finrank ℂ G := by
  obtain ⟨e, _⟩ := h.eigenspace_equiv E G hG
  exact e.finrank_eq.symm

theorem transfer_ground_exactly_two {b L coupling : ℝ} {v : Potential}
    (h : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hG : GroundSpaceExactlyTwo b v L coupling) :
    Module.finrank ℂ (operatorEigenspace
      (magneticOperator b coupling (doubleWellPotential v L)) (groundEnergy b v L coupling)) = 2 := by
  obtain ⟨G, hspace, hdim, _⟩ := hG
  rw [h.eigenspace_finrank (groundEnergy b v L coupling) G hspace, hdim]

theorem transfer_simple_ground {b L coupling : ℝ} {v : Potential} {even : Bool}
    (h : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hG : SimpleGroundParity b v L coupling even) :
    Module.finrank ℂ (operatorEigenspace
      (magneticOperator b coupling (doubleWellPotential v L)) (groundEnergy b v L coupling)) = 1 := by
  obtain ⟨G, hspace, hdim, _⟩ := hG
  rw [h.eigenspace_finrank (groundEnergy b v L coupling) G hspace, hdim]

theorem IsMagneticRealization.transfer_normalized_parity_eigenfunction
    {b coupling E : ℝ} {V : Potential} {ψ : Wavefunction} {even : Bool}
    (h : IsMagneticRealization b coupling V) (hψ : IsEigenfunction b coupling V E ψ)
    (hm : mass ψ = 1) (hp : HasParity even ψ) :
    ∃ u : L2Space, u ∈ operatorEigenspace (magneticOperator b coupling V) E ∧
      u ≠ 0 ∧ HasL2Parity even u := by
  let u : L2Space := hψ.2.1.toLp ψ
  have hu : Represents u ψ := hψ.2.1.coeFn_toLp
  exact ⟨u, (h.eigenfunction_iff E u).mpr ⟨ψ, hψ, hu⟩,
    hu.ne_zero_of_mass_one hm, hu.hasL2Parity hp⟩

theorem transfer_ground_parity_modes {b L coupling : ℝ} {v : Potential}
    (h : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hG : GroundSpaceExactlyTwo b v L coupling) :
    ∃ uEven uOdd : L2Space,
      uEven ∈ operatorEigenspace (magneticOperator b coupling (doubleWellPotential v L))
        (groundEnergy b v L coupling) ∧
      uOdd ∈ operatorEigenspace (magneticOperator b coupling (doubleWellPotential v L))
        (groundEnergy b v L coupling) ∧
      uEven ≠ 0 ∧ uOdd ≠ 0 ∧ HasL2Parity true uEven ∧ HasL2Parity false uOdd := by
  obtain ⟨G, hspace, _, ψEven, ψOdd, heG, hoG, hem, hom, hep, hop⟩ := hG
  obtain ⟨uEven, heu, hen, hepar⟩ := h.transfer_normalized_parity_eigenfunction
    ((hspace ψEven).mp heG) hem hep
  obtain ⟨uOdd, hou, hon, hopar⟩ := h.transfer_normalized_parity_eigenfunction
    ((hspace ψOdd).mp hoG) hom hop
  exact ⟨uEven, uOdd, heu, hou, hen, hon, hepar, hopar⟩

end InfiniteZero
