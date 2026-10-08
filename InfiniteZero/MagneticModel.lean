import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Concrete magnetic Schrödinger model

This file fixes the physical quantities appearing in the active `thm:main` of
`Infinite_Zero_Tunneling_Lean_oriented_V2.tex`, §`sec:introduction`. Throughout,
`coupling` is the manuscript's positive parameter `λ`; `b` is fixed, the magnetic
field is `bλ`, and the electric potential is multiplied by `λ²`. The energies
here use the original, unscaled normalization. Dividing by `λ²` gives the
semiclassical normalization with `h = λ⁻¹` used in the body of the manuscript.
The definitions themselves also make sense for other real parameter values;
positivity and large-coupling conditions are imposed by the theorems using them.

The differential expression, quadratic form, variational energies, and hopping
integral are concrete definitions. `SpectralRealization` records the eventual
relations between the variational levels and parity eigenspaces; the later
construction proves those relations for the fixed potential. It is not an
assumption built into these definitions.

Eigenfunctions here are smooth, complex-valued, square-integrable functions,
with their differential equation holding at every point. `OperatorBridge.lean`
connects this description to the actual unbounded operator on physical `L²`.
That classical connection is admission A002; the spectral and tunneling
properties of the constructed potential are proved separately. For a statement
review, continue from this file to `MainConclusion` and
`OperatorMainConclusion`; `docs/STATEMENT_AUDIT.md` records the exact scope.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace InfiniteZero

/-- Physical `ℝ²` with its Euclidean norm. Lean coordinates `0, 1` are the
manuscript's coordinates `1, 2`; integrals use planar Lebesgue measure. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A real electric potential on the physical plane; smoothness and support
conditions are separate properties, such as `AdmissiblePotential`. -/
abbrev Potential := Plane → ℝ

/-- A complex-valued function on the physical plane. Regularity, square
integrability, and normalization are imposed separately when needed. -/
abbrev Wavefunction := Plane → ℂ

/-- The single-well requirements `v ∈ C_c^∞(ℝ²; [-1,0])`, with `v` nonradial,
from the active TeX `thm:main`. This predicate contains no spectral or tunneling
hypothesis. The explicit core-plus-cusps construction proves these properties.
It does not itself require a unique minimum or specify its value; any stronger
geometric facts needed in the proof are established for the constructed `v`. -/
structure AdmissiblePotential (v : Potential) : Prop where
  /-- All real derivatives of `v` exist and are continuous. -/
  smooth : ContDiff ℝ ∞ v
  /-- The closure of the set where `v` is nonzero is compact. -/
  compactSupport : HasCompactSupport v
  /-- Pointwise bounds `-1 ≤ v(x) ≤ 0`, including points outside the support. -/
  range : ∀ x, v x ∈ Icc (-1) 0
  /-- Two points on the same circle have different potential values, so `v`
  cannot be a function of the distance to the origin alone. -/
  nonradial : ∃ x y, ‖x‖ = ‖y‖ ∧ v x ≠ v y

/-- The `i`th Euclidean unit coordinate vector. -/
def coordinateVector (i : Fin 2) : Plane := EuclideanSpace.single i 1

/-- The displacement `d = (L,0)` in TeX `eq:double-well-unscaled`; the two
well centers are `-d` and `d`, separated by `2L` when `L > 0`. -/
def displacement (L : ℝ) : Plane := L • coordinateVector 0

/-- The oriented area `x ∧ y = x₁y₂ - x₂y₁`, with the sign convention used
in the magnetic phase in TeX `eq:magnetic-translation`. -/
def wedge (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

/-- The `i`th coordinate of `x^⊥ = (-x₂,x₁)` in the symmetric gauge. -/
def perpCoordinate (x : Plane) (i : Fin 2) : ℝ :=
  if i = 0 then -x 1 else x 0

/-- The partial derivative is the real Fréchet derivative in a coordinate direction. -/
def partialDerivative (i : Fin 2) (ψ : Wavefunction) (x : Plane) : ℂ :=
  fderiv ℝ ψ x (coordinateVector i)

/-- The unscaled covariant momentum `Dᵢ = -i ∂ᵢ - (bλ/2)(x^⊥)ᵢ`, with
`λ = coupling`. This is a momentum component, including the factor `-i`,
rather than a covariant derivative with that factor removed. -/
def covariantDerivative (b coupling : ℝ) (i : Fin 2) (ψ : Wavefunction) : Wavefunction :=
  fun x => -Complex.I * partialDerivative i ψ x -
    ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ) * ψ x

/-- The differential expression `Σᵢ Dᵢ² ψ + λ² V ψ`, with `λ = coupling`.
For `V = v` this is TeX `eq:one-well-unscaled`; for
`V = doubleWellPotential v L` it is `eq:double-well-unscaled`.
This is an operation on functions; its closed operator domain on `L²` is
defined separately by `magneticOperator` in `OperatorBridge.lean`. -/
def magneticHamiltonian (b coupling : ℝ) (V : Potential) (ψ : Wavefunction) : Wavefunction :=
  fun x => (∑ i : Fin 2, covariantDerivative b coupling i (covariantDerivative b coupling i ψ) x) +
    ((coupling ^ 2 * V x : ℝ) : ℂ) * ψ x

/-- The unscaled electric profile `v(x+d) + v(-x+d)` from TeX
`eq:double-well-unscaled` / `eq:translated-potentials`, before multiplication
by `λ²`. Inversion exchanges the two terms even when `v` is nonradial. -/
def doubleWellPotential (v : Potential) (L : ℝ) : Potential :=
  fun x => v (x + displacement L) + v (-x + displacement L)

theorem doubleWellPotential_inversion (v : Potential) (L : ℝ) (x : Plane) :
    doubleWellPotential v L (-x) = doubleWellPotential v L x := by
  simp only [doubleWellPotential, neg_neg, add_comm]

/-- TeX `H_v(λ)` as a classical differential expression, with fixed
displacement `d = (L,0)` and the two translated electric wells. -/
def doubleHamiltonian (b : ℝ) (v : Potential) (L coupling : ℝ) :
    Wavefunction → Wavefunction :=
  magneticHamiltonian b coupling (doubleWellPotential v L)

/-- Squared physical `L²` norm, with planar Lebesgue measure. -/
def mass (ψ : Wavefunction) : ℝ := ∫ x : Plane, ‖ψ x‖ ^ 2

/-- The physical complex inner product `⟨ψ,χ⟩ = ∫ conjugate(ψ) χ`, conjugate
linear in the first argument, as in the hopping formula `eq:rho-intro`. -/
def waveInner (ψ χ : Wavefunction) : ℂ :=
  ∫ x : Plane, star (ψ x) * χ x

/-- Membership in the test-function core `C_c^∞(ℝ²; ℂ)`. -/
def IsTestFunction (ψ : Wavefunction) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ

/-- A smooth compactly supported test function with physical `L²` norm one. -/
def IsNormalizedTest (ψ : Wavefunction) : Prop :=
  IsTestFunction ψ ∧ mass ψ = 1

/-- The unscaled energy form
`q_{b,λ,V}(ψ) = ∫ (Σᵢ |Dᵢψ|² + λ² V |ψ|²)`.
On smooth compactly supported functions and smooth bounded `V`, integration
by parts identifies it with `Re ⟨ψ,Hψ⟩`. This definition is an integral on
functions, not a separately assumed closed form or operator domain. -/
def magneticForm (b coupling : ℝ) (V : Potential) (ψ : Wavefunction) : ℝ :=
  ∫ x : Plane, (∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2) +
    coupling ^ 2 * V x * ‖ψ x‖ ^ 2

/-- The infimum of `q_{b,λ,V}(ψ)` over normalized `C_c^∞` functions.
For the smooth bounded potentials in the theorem, the classical realization
certificate `IsMagneticRealization.bottom_eq` identifies this with the
Rayleigh infimum on the closed operator domain. Eigenvalue attainment and
isolation are additional results proved later, not part of this definition. -/
def variationalBottom (b coupling : ℝ) (V : Potential) : ℝ :=
  sInf {E | ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ magneticForm b coupling V ψ = E}

/-- The one-well variational ground energy in the unscaled units of TeX
`eq:one-well-unscaled`. It is `λ²` times the semiclassical atomic energy `E_h`
used in `eq:one-well-equations`, with `h = λ⁻¹`. -/
def atomicGroundEnergy (b : ℝ) (v : Potential) (coupling : ℝ) : ℝ :=
  variationalBottom b coupling v

/-- The double-well variational bottom, corresponding to the lowest level
`E₀(λ)` in the introduction. The final operator conclusion separately proves
that this level is attained and isolated for sufficiently large coupling. -/
def groundEnergy (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  variationalBottom b coupling (doubleWellPotential v L)

/-- Parity under full spatial inversion `x ↦ -x`: `true` means
`ψ(-x) = ψ(x)` and `false` means `ψ(-x) = -ψ(x)`. This is the symmetry
`𝒫` from TeX §`sec:scaled-double-well`, not reflection in just one axis
and not complex conjugation. -/
def HasParity (even : Bool) (ψ : Wavefunction) : Prop :=
  ∀ x, ψ (-x) = if even then ψ x else -ψ x

/-- The infimum of the double-well form over normalized smooth compactly
supported functions of the chosen parity. This is the variational counterpart
of `E_even(λ)` / `E_odd(λ)` in the introduction. It is not defined using the
Mathlib spectrum; the construction later proves attainment by actual parity
eigenfunctions and the needed lower bounds. -/
def parityEnergy (b : ℝ) (v : Potential) (L coupling : ℝ) (even : Bool) : ℝ :=
  sInf {E | ∃ ψ : Wavefunction,
    IsNormalizedTest ψ ∧ HasParity even ψ ∧
    magneticForm b coupling (doubleWellPotential v L) ψ = E}

/-- The even-sector variational bottom, TeX `E_even(λ)`. -/
def evenEnergy (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  parityEnergy b v L coupling true

/-- The odd-sector variational bottom, TeX `E_odd(λ)`. -/
def oddEnergy (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  parityEnergy b v L coupling false

/-- TeX `S_v(λ) = E_odd(λ) - E_even(λ)` from
`eq:signed-splitting-intro`. A positive value favors an even ground state;
a negative value favors an odd one. Its absolute value is the lowest
doublet gap once the min/max identities in `SpectralRealization` hold. -/
def signedSplitting (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  oddEnergy b v L coupling - evenEnergy b v L coupling

/-- The second min-max value: the infimum, over complex two-dimensional
subspaces of `C_c^∞`, of all upper bounds for the form on their normalized
vectors. This is the variational counterpart of `E₁(λ)`, counted with
multiplicity, in TeX `thm:main(i)`. The definition does not choose a spectral
enumeration. The later construction proves that it equals the maximum of
the two parity energies, while `groundEnergy` equals their minimum. -/
def secondEnergy (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  sInf {E | ∃ F : Submodule ℂ Wavefunction,
    Module.finrank ℂ F = 2 ∧
    (∀ ψ ∈ F, IsTestFunction ψ) ∧
    (∀ ψ ∈ F, mass ψ = 1 → magneticForm b coupling (doubleWellPotential v L) ψ ≤ E)}

/-- The pointwise equation `Hψ = Eψ`, with real energy `E` and a smooth
complex-valued `L²` function `ψ`. No reality or positivity of `ψ` is imposed.
The zero function is included so that the predicate describes a full complex
eigenspace; normalized or nonzero eigenvectors are requested separately.
`IsMagneticRealization.eigenfunction_iff` supplies the correspondence with
eigenvectors of the closed operator on `L²`. -/
def IsEigenfunction (b coupling : ℝ) (V : Potential) (E : ℝ) (ψ : Wavefunction) : Prop :=
  ContDiff ℝ ∞ ψ ∧ MemLp ψ 2 volume ∧
    ∀ x, magneticHamiltonian b coupling V ψ x = (E : ℂ) * ψ x

/-- `IsEigenfunction` for the two-well differential expression `H_v(λ)`.
The energy `E` remains in unscaled units. -/
def IsDoubleEigenfunction (b : ℝ) (v : Potential) (L coupling E : ℝ)
    (ψ : Wavefunction) : Prop :=
  IsEigenfunction b coupling (doubleWellPotential v L) E ψ

/-- A normalized smooth `L²` eigenfunction of the one-well Hamiltonian at
its actual variational bottom. This is the atomic state `φ_h` used to form
the left and right orbitals in TeX `eq:translated-states`; multiplying the
Hamiltonian by `h²` changes the energy but not the normalized eigenfunction.
The state may be complex and its existence is not built into the predicate. -/
def IsAtomicGroundState (b : ℝ) (v : Potential) (coupling : ℝ) (φ : Wavefunction) : Prop :=
  IsEigenfunction b coupling v (atomicGroundEnergy b v coupling) φ ∧ mass φ = 1

/-- A classical choice of normalized atomic ground state, depending only on
`b`, `v`, and `λ`, whenever such a state exists; otherwise the value is zero.
This makes the hopping a total function of `λ`. The `atomic_states` field of
`MainConclusion` proves existence at all sufficiently large couplings, so the
fallback is excluded on the tail relevant to the theorem. No continuity or
preferred phase of this choice is assumed; `hopping_intrinsic` later proves
that any normalized atomic ground state gives the same hopping coefficient. -/
def canonicalAtomicState (b : ℝ) (v : Potential) (coupling : ℝ) : Wavefunction := by
  classical
  exact if h : ∃ φ : Wavefunction, IsAtomicGroundState b v coupling φ then
    Classical.choose h
  else 0

theorem canonicalAtomicState_spec (b : ℝ) (v : Potential) (coupling : ℝ)
    (h : ∃ φ : Wavefunction, IsAtomicGroundState b v coupling φ) :
    IsAtomicGroundState b v coupling (canonicalAtomicState b v coupling) := by
  simpa only [canonicalAtomicState, dif_pos h] using Classical.choose_spec h

/-- TeX `eq:magnetic-translation`:
`T_a φ(x) = exp(-i bλ (x ∧ a)/2) φ(x-a)`, with `h = λ⁻¹`.
The negative sign in the phase matches the momentum `P - bλ x^⊥/2`.
Translation and multiplication by this unit-modulus phase preserve `L²`
normalization; their analytic properties are proved in `MagneticCovariance`. -/
def magneticTranslation (b coupling : ℝ) (a : Plane) (φ : Wavefunction) : Wavefunction :=
  fun x => Complex.exp (-Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ)) * φ (x - a)

/-- The left orbital `φ_h^L = T_{-d} φ_h` from TeX
`eq:translated-states`, centered at `-d` with `d = (L,0)`. -/
def leftState (b L coupling : ℝ) (φ : Wavefunction) : Wavefunction :=
  magneticTranslation b coupling (-displacement L) φ

/-- The right orbital `φ_h^R(x) = φ_h^L(-x)` from TeX
`eq:translated-states`. It uses the very same atomic state as `leftState`,
followed by inversion, without complex conjugation. -/
def rightState (b L coupling : ℝ) (φ : Wavefunction) : Wavefunction :=
  fun x => leftState b L coupling φ (-x)

/-- The actual complex hopping integral
`ρ_λ = λ² ∫ conjugate(φ_h^L(x)) v(x+d) φ_h^R(x) dx`
from TeX `eq:rho-intro`. The factor is `λ² = h⁻²`, so this is the unscaled
`ρ_λ`, not the scaled `ρ̂_h` of `eq:rho-scaled`. Both orbitals use the same
input state `φ`. Reality and independence of its normalized ground-state
choice are proved later; neither is imposed by taking a real part here. -/
def hopping (b : ℝ) (v : Potential) (L coupling : ℝ) (φ : Wavefunction) : ℂ :=
  (coupling ^ 2 : ℝ) * ∫ x : Plane,
    star (leftState b L coupling φ x) * (v (x + displacement L) : ℂ) * rightState b L coupling φ x

/-- The real part of `hopping`, used in real-variable oscillation arguments.
The main theorem's hopping zeros are equalities for the full complex
coefficient `canonicalHopping`, not merely zeros of this real part. -/
def hoppingReal (b : ℝ) (v : Potential) (L coupling : ℝ) (φ : Wavefunction) : ℝ :=
  (hopping b v L coupling φ).re

/-- The hopping integral evaluated on `canonicalAtomicState`, giving a fixed
complex-valued function of `λ`. `MainConclusion.atomic_states` and
`MainConclusion.hopping_intrinsic` certify on a sufficiently large tail
that it is the physical coefficient and agrees with the integral formed
from every normalized atomic ground state. -/
def canonicalHopping (b : ℝ) (v : Potential) (L coupling : ℝ) : ℂ :=
  hopping b v L coupling (canonicalAtomicState b v coupling)

/-- The complex submodule `G` consists of all and only the smooth `L²`
solutions of the double-well eigenvalue equation at `groundEnergy`.
Thus `G` is the full physical classical eigenspace, not a selected subspace
of modes. The operator realization later transfers it to the full `L²`
operator eigenspace. -/
def IsGroundEigenspace (b : ℝ) (v : Potential) (L coupling : ℝ)
    (G : Submodule ℂ Wavefunction) : Prop :=
  ∀ ψ, ψ ∈ G ↔ IsDoubleEigenfunction b v L coupling (groundEnergy b v L coupling) ψ

/-- The classical-eigenfunction content of the multiplicity assertion in
TeX `thm:main(i)`: the full ground eigenspace has complex dimension two,
with normalized even and odd eigenfunctions. This predicate specifies the
dimension and parity content; isolation is supplied separately by
`HasGapAboveGround` in the final `OperatorMainConclusion`. -/
def GroundSpaceExactlyTwo (b : ℝ) (v : Potential) (L coupling : ℝ) : Prop :=
  ∃ G : Submodule ℂ Wavefunction,
    IsGroundEigenspace b v L coupling G ∧ Module.finrank ℂ G = 2 ∧
    ∃ ψEven ψOdd : Wavefunction,
      ψEven ∈ G ∧ ψOdd ∈ G ∧ mass ψEven = 1 ∧ mass ψOdd = 1 ∧
      HasParity true ψEven ∧ HasParity false ψOdd

/-- The full classical ground eigenspace is a complex line, containing a
normalized state of the prescribed inversion parity. Alternating occurrences
with `even = true` and `even = false` express the parity changes in TeX
`thm:main(iii)`; `OperatorMainConclusion` also transfers this to `L²`. -/
def SimpleGroundParity (b : ℝ) (v : Potential) (L coupling : ℝ) (even : Bool) : Prop :=
  ∃ G : Submodule ℂ Wavefunction,
    IsGroundEigenspace b v L coupling G ∧ Module.finrank ℂ G = 1 ∧
    ∃ ψ : Wavefunction, ψ ∈ G ∧ mass ψ = 1 ∧ HasParity even ψ

/-- The eventual doublet identities needed to interpret the variational
energies in TeX `thm:main(i,iii)`. On the tail `λ ≥ threshold`, the first
two min-max levels are the min/max of the parity energies, equality gives
a double ground eigenspace, and strict inequality gives a simple ground
state in the lower sector. These are results to prove for the constructed
potential, not the classical operator-realization admission A002.
The final assembly constructs this certificate. The separate positive gap
and `L²` operator interpretation appear in `OperatorMainConclusion`. -/
structure SpectralRealization (b : ℝ) (v : Potential) (L threshold : ℝ) : Prop where
  /-- The first min-max level is the lower parity energy. -/
  ordered_ground : ∀ coupling, threshold ≤ coupling →
    groundEnergy b v L coupling = min (evenEnergy b v L coupling) (oddEnergy b v L coupling)
  /-- The second min-max level is the higher parity energy, also at equality. -/
  ordered_second : ∀ coupling, threshold ≤ coupling →
    secondEnergy b v L coupling = max (evenEnergy b v L coupling) (oddEnergy b v L coupling)
  /-- Every equality of parity energies on this tail has exactly two ground
  modes, with opposite parities; this is not restricted to a chosen sequence. -/
  crossing : ∀ coupling, threshold ≤ coupling → evenEnergy b v L coupling = oddEnergy b v L coupling →
    GroundSpaceExactlyTwo b v L coupling
  /-- If the even energy is strictly lower, the full ground eigenspace is
  one-dimensional and even. -/
  even_lower : ∀ coupling, threshold ≤ coupling → evenEnergy b v L coupling < oddEnergy b v L coupling →
    SimpleGroundParity b v L coupling true
  /-- If the odd energy is strictly lower, the full ground eigenspace is
  one-dimensional and odd. -/
  odd_lower : ∀ coupling, threshold ≤ coupling → oddEnergy b v L coupling < evenEnergy b v L coupling →
    SimpleGroundParity b v L coupling false

end InfiniteZero
