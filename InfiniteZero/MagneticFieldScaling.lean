import InfiniteZero.OperatorBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Reduction to unit magnetic field

For a nonzero fixed field parameter `b`, the model at coupling `λ` is exactly
the unit-field model at coupling `b * λ` with electric profile `V / b²`.
This is a change of parameters, with no change of coordinates, states or
energy units. When `b > 0`, large positive `λ` corresponds to large positive
unit-field coupling. These identities provide the algebraic conversion used
when applying unit-field one-well spectral estimates to the radial core.
-/

noncomputable section

namespace InfiniteZero

/-- Replacing `(b, λ)` by `(1, bλ)` leaves each magnetic momentum unchanged. -/
theorem covariantDerivative_unitField (b coupling : ℝ) (i : Fin 2)
    (ψ : Wavefunction) :
    covariantDerivative b coupling i ψ = covariantDerivative 1 (b * coupling) i ψ := by
  funext x
  simp only [covariantDerivative, one_mul]

/-- Exact conversion of the differential expression to unit field.
The potential factor satisfies `(bλ)² (V/b²) = λ² V`. -/
theorem magneticHamiltonian_unitField {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) (ψ : Wavefunction) :
    magneticHamiltonian b coupling V ψ =
      magneticHamiltonian 1 (b * coupling) (fun x => V x / b ^ 2) ψ := by
  have hV (x : Plane) : (b * coupling) ^ 2 * (V x / b ^ 2) = coupling ^ 2 * V x := by
    field_simp
  funext x
  simp only [magneticHamiltonian, covariantDerivative_unitField b coupling, hV]

/-- The quadratic forms agree on the same functions under the unit-field
reparametrization; no regularity or integrability assumption is required. -/
theorem magneticForm_unitField {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) (ψ : Wavefunction) :
    magneticForm b coupling V ψ =
      magneticForm 1 (b * coupling) (fun x => V x / b ^ 2) ψ := by
  have hV (x : Plane) : (b * coupling) ^ 2 * (V x / b ^ 2) = coupling ^ 2 * V x := by
    field_simp
  simp only [magneticForm, covariantDerivative_unitField b coupling, hV]

/-- Equality of variational bottoms follows from equality of the test forms. -/
theorem variationalBottom_unitField {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) :
    variationalBottom b coupling V =
      variationalBottom 1 (b * coupling) (fun x => V x / b ^ 2) := by
  simp only [variationalBottom, magneticForm_unitField hb coupling V]

/-- The unscaled one-well ground energy is unchanged by the unit-field
reparametrization. -/
theorem atomicGroundEnergy_unitField {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) :
    atomicGroundEnergy b V coupling =
      atomicGroundEnergy 1 (fun x => V x / b ^ 2) (b * coupling) :=
  variationalBottom_unitField hb coupling V

/-- Smooth square-integrable eigenfunctions and their energies are unchanged. -/
theorem isEigenfunction_unitField_iff {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) (E : ℝ) (ψ : Wavefunction) :
    IsEigenfunction b coupling V E ψ ↔
      IsEigenfunction 1 (b * coupling) (fun x => V x / b ^ 2) E ψ := by
  simp only [IsEigenfunction, magneticHamiltonian_unitField hb coupling V]

/-- A normalized atomic ground state is the same function in either
parametrization. -/
theorem isAtomicGroundState_unitField_iff {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) (ψ : Wavefunction) :
    IsAtomicGroundState b V coupling ψ ↔
      IsAtomicGroundState 1 (fun x => V x / b ^ 2) (b * coupling) ψ := by
  simp only [IsAtomicGroundState, atomicGroundEnergy_unitField hb coupling V,
    isEigenfunction_unitField_iff hb coupling V]

/-- The concrete test-function graph is unchanged, including its `L²`
representatives. -/
theorem magneticTestGraph_unitField {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) :
    magneticTestGraph b coupling V =
      magneticTestGraph 1 (b * coupling) (fun x => V x / b ^ 2) := by
  simp only [magneticTestGraph, magneticHamiltonian_unitField hb coupling V]

/-- Taking the closed linear span preserves the equality of test graphs. -/
theorem magneticClosedGraph_unitField {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) :
    magneticClosedGraph b coupling V =
      magneticClosedGraph 1 (b * coupling) (fun x => V x / b ^ 2) := by
  simp only [magneticClosedGraph, magneticTestGraph_unitField hb coupling V]

/-- The closed magnetic operators are equal as partial linear maps on `L²`.
This includes equality of their domains and does not use the realization
admission. -/
theorem magneticOperator_unitField {b : ℝ} (hb : b ≠ 0) (coupling : ℝ)
    (V : Potential) :
    magneticOperator b coupling V =
      magneticOperator 1 (b * coupling) (fun x => V x / b ^ 2) := by
  simp only [magneticOperator, magneticClosedGraph_unitField hb coupling V]

end InfiniteZero
