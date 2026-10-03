# A004 — classical spectral data for the radial core

The existence of the
`RadialCoreSpectralData` contract is the classical admitted result **A004**,
`InfiniteZero.radial_core_spectral_data`, in
[`Remaining.lean`](../InfiniteZero/Remaining.lean). The informal proof
below justifies all its fields using the published radial magnetic harmonic
approximation and the connections to the realization and min-max principle. This
informal proof is not a Lean proof of the admitted result.

The contract includes a real, radial, strictly positive choice of ground
state, at the same threshold. It assumes neither its exterior radial equation,
nor the integrability of its profile with respect to the measure `r dr`, nor a
formula in terms of Γ: these connections remain separate Lean proofs.

The passage to the simple ground state of the full potential and its gap is
proved in Lean from this contract and the operator realizations A002.
A004 contains no nonradial, source, or tunneling result.
The integrability of the energy density of a noncompact eigenstate is
neither a field of the contract nor an assumption of this construction.

## 1. Checked primary references

In [Helffer–Kachmar, arXiv:2208.13030v5](https://arxiv.org/pdf/2208.13030v5), the radial hypotheses appear in (1.1), p. 1. Theorem 1.1(1–2), p. 3, gives simplicity, energy, and the existence of a positive normalized radial ground state for every `0<ε≤ε₀`. Its part (2) directly justifies the positive radial choice. Proposition 2.1, pp. 11–12, gives the harmonic approximation of each fixed min-max level and radiality: apply levels 1 and 2 for the gap. Remark 1.6, pp. 7–8, describes the change of constant field. Only the single-well part is used; the WKB expansion in part (3) is not admitted here.

For the differential realization, [Shubin, arXiv:math/0007019v2](https://arxiv.org/pdf/math/0007019v2), Lemma 5.1 and Theorem 5.2, p. 10, provide local regularity and essential self-adjointness in a more general setting; the cutoff identity (5.3), p. 12, is compatible with the form argument below. Our potential is smooth and bounded, the magnetic field is smooth, and Euclidean space is complete. Elliptic regularity can then be bootstrapped to a smooth representative.

Page numbers are those printed in the PDFs.

## 2. Admitted Lean contract and exact scope

The exact definition is
[`RadialCoreSpectralData`](../InfiniteZero/RadialCoreSpectralData.lean).
It fixes `γ>0`, `B>0`, and `T>0`. The unchanged `ground` field requires,
for each `λ≥T`, a state
`φ` such that, with `e=λ⁻² atomicGroundEnergy b p.core λ`:

- `IsAtomicGroundState b p.core λ φ`;
- `e ≤ −1+B/λ`;
- for every test function `u`,
  `γλ (mass u − ‖waveInner φ u‖²) ≤ magneticForm b λ p.core u − λ²e mass u`.

The separate added field is exactly:

```lean
positive_radial_ground : ∀ coupling, threshold ≤ coupling → ∃ φ,
  IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ
```

In [`RealRadialState.lean`](../InfiniteZero/RealRadialState.lean),
`realRadialProfile φ r := (φ (r • coordinateVector 0)).re`, and
`IsPositiveRadial φ` contains the two pointwise properties

```lean
radial : ∀ x, φ x = (realRadialProfile φ ‖x‖ : ℂ)
positive : ∀ x, 0 < (φ x).re
```

The first also forces the function to be real-valued. These properties concern
the actual smooth representative, including at the origin. The witnesses for
`ground` and `positive_radial_ground` are independent: no equality between
them, or positive phase for the arbitrary choice `canonicalAtomicState`, is
asserted. Using them together will require a proved identification up to
phase, or the explicit selection of the positive witness.

The admitted declaration is exactly:

```lean
theorem radial_core_spectral_data (b : ℝ) (p : CuspParameters)
    (hb : 0 < b) (hr : 0 < p.r₀) : Nonempty (RadialCoreSpectralData b p) := by
  sorry
```

Only `b>0` and `p.r₀>0` are required. The other fields of `p` do not enter
`p.core`; no condition on the cusps is imported.
`IsAtomicGroundState` includes smoothness, membership in L², the pointwise
equation at the energy defined by the variational infimum, and `mass φ=1`.
The threshold and constants are chosen before the coupling and the state.
The new field adds no continuity in the coupling, profile bound, or
exponential estimate. The proofs of the first transfer continue to use
`ground` without having to choose its phase.

For `b=p.b`, `BasicConditions`, and the two operator realizations,
`AtomicGroundConstruction.eventual_atomicGround_properties_of_radialData`
constructs the ground state of the full potential, its simplicity,
its gap, and the inequality between its energy and that of the core.
`exists_atomicGroundCertificate_of_radialData` retains the gap `γλ/2`.
The exterior-mass inequality comes from the radial closed graph, without
`Integrable (magneticEnergyDensity … φ)` or an integral identity for `φ`.
`CuspParameters.eventual_atomicGround_properties`, in `Remaining.lean`,
provides these atomic conclusions from `BasicConditions` alone using
A002 and A004. The contract provides no exponential, source,
hopping, or double-well estimate.

## 3. Independent calculation of scales and constants

Set `V = p.core`, `r₀ = p.r₀`, `h = λ⁻¹`, and `A(x) = x^⊥/2`. The repository's differential model is

\[
 H_\lambda=(-i\nabla-b\lambda A)^2+\lambda^2V,
 \qquad H_h=(-ih\nabla-bA)^2+V=h^2H_\lambda.
\]

The algebraic identity that allows the unit-field theorem to be applied is

\[
 H_h=b^2\bigl((-i(h/b)\nabla-A)^2+V/b^2\bigr).
\]

Thus the parameter in the published theorem is `ε=h/b=1/(bλ)` for the
potential `V/b²`. Equivalently, `Hλ=(bλ)² Lε^(V/b²)`. This reduction
multiplies the operator by a positive scalar; it changes neither the
eigenfunction nor its L² normalization. No spatial dilation is required
to transfer its radiality and positivity.

The core equals `−exp(−|x|²/(r₀²−|x|²))` inside the ball and zero outside. It is radial, smooth, and compactly supported, with a unique minimum `−1`, and

\[
 V(x)=-1+|x|^2/r_0^2+O(|x|^4),\qquad
 (V/b^2)''(0)=2/(b^2r_0^2).
\]

The lemmas `core_contDiff`, `core_hasCompactSupport`, `core_range`, `core_zero`, and `core_gt_neg_one` verify the first properties. The module
[`CoreRadialHypotheses`](../InfiniteZero/CoreRadialHypotheses.lean) also proves
the exact radiality `p.core x = p.coreRadialProfile ‖x‖`, the smoothness and
compact support of the profile, its strict minimum, and
`iteratedDeriv 2 p.coreRadialProfile 0 = 2 / p.r₀² > 0`.
These verifications use only `r₀>0`, with no admitted result. The Taylor
remainder displayed here is an informal calculation, not a new Lean theorem
being presented as proved.

The unitary transformation in dimension two is

\[
 (U_h f)(y)=h^{1/2}f(\sqrt h\,y).
\]

After this dilation, the limiting oscillator is

\[
 Q_b=(-i\nabla-bA)^2+|y|^2/r_0^2.
\]

With `ν = √(b²/4 + r₀⁻²)`, its levels are
`2ν(2n + |m| + 1) − bm`, for `n ≥ 0`, `m ∈ ℤ`. Its ground-state energy is `μ₀ = 2ν` and its first gap is `δ₀ = 2ν − b > 0`. This identification of the second level uses the full spectrum of the oscillator; checking only a Gaussian eigenfunction would not suffice. All explicit constants can be avoided by simply retaining the strictly positive difference between the first two oscillator levels.

Applying the result to the first two levels gives

\[
 e_1(h)=-1+\mu_0h+O(h^{3/2}),\qquad
 e_2(h)-e_1(h)=\delta_0h+O(h^{3/2}).
\]

One may therefore take `γ = δ₀/2` and `B = μ₀+1`, then choose `h₀ > 0` small enough that `e₁(h) ≤ −1+Bh` and `e₂(h)−e₁(h) ≥ γh` for `0<h<h₀`. Choosing `T ≥ max(1,2/h₀)` ensures these bounds for every `λ≥T`, including at the closed threshold. The unscaled energies are `Λⱼ(λ)=λ²eⱼ(1/λ)`, so the gap becomes `γλ`, not `γ/λ`.

If `ε₀>0` is the threshold for the positive ground state for `V/b²`, choosing
the common threshold `T ≥ max(T_ancien, 1/(bε₀), 1)` preserves all the
properties of `ground` and ensures `0<1/(bλ)≤ε₀` for each `λ≥T`.
The constants and threshold depend on `b` and the fixed core; no uniformity
as `b` or `r₀` vary is asserted.

## 4. Min-max identification, graph, and test functions

### 4.1 Same operator, same energy

The operator in the paper is the self-adjoint realization of the same initial differential operator on `C∞c`. Essential self-adjointness identifies its closure with the repository's concrete graph. The existing admitted result A002, `magnetic_realization`, already contains `graph_eq`, `selfAdjoint`, `bottom_eq`, and `eigenfunction_iff`; it creates no eigenvector and asserts no gap.

`bottom_eq` relates the infimum of the operator quotients to the infimum over the test functions in `atomicGroundEnergy`. Once the operator has been identified, the ground-state energy in the paper is therefore the Lean energy. Independently, equality of the infima follows from the variational principle and approximation of the ground state by the core `C∞c` in the graph norm. This connection is essential: a spectral result for an unidentified abstract operator would not suffice to populate `IsAtomicGroundState`.

Elliptic regularity, or the `eigenfunction_iff` field of A002, gives a smooth representative. The almost-everywhere equality in the equation becomes pointwise by continuity. Identifying the `L²` norm with `mass` transfers its normalization.

### 4.2 Positive radial choice: justification of the separate field

Simplicity and rotational invariance alone do not suffice to force the
zero angular sector. The argument in Proposition 2.1 additionally uses
closeness to the radial ground state of the limiting oscillator to
identify this sector when the parameter is small. Theorem 1.1(2)
then directly provides the positive normalized choice.

To understand positivity, in the radial sector the magnetic expression
becomes the real operator `−ε²Δ+|x|²/4+V/b²`. The choice of a positive
phase is explained by the variational principle and the maximum principle
for this scalar problem. The origin is handled in the planar elliptic
equation, without using an ODE singular at `r=0`. This reasoning does not
assume that the general magnetic semigroup preserves positivity.

After the operator identification in §4.1, the smooth positive representative
from the classical result and the representative from A002 coincide almost
everywhere, hence everywhere by continuity and the full support of Lebesgue
measure. This transfers exactly the two fields of `IsPositiveRadial`. The
real restriction to the axis then provides `realRadialProfile`; its regularity
follows from composition with the linear map `r ↦ r e₀`, and is not an
additional spectral field.

### 4.3 Exterior mass: the connection to the graph is proved

The exterior mass bound follows by extending a test-function inequality
to the closed operator graph. For a test function `ψ`,
kinetic positivity, `p.core≥−1`, and the vanishing of the core outside
its ball give

\[
 \lambda^2\|1_{|x|\ge r_0}\psi\|_2^2
 \le \operatorname{Re}\langle\psi,H_\lambda\psi\rangle
       +\lambda^2\|\psi\|_2^2.
\]

Both sides are continuous as functions of the pair `(ψ,Hλψ)` in L²×L²:
restriction to a measurable set is a bounded operator.
`AtomicExteriorGraph.core_exteriorMass_closedGraph` therefore extends this
inequality to the closure of the test-function graph. For the normalized
eigenvector, `core_exteriorMass_le_of_atomicGroundState` concludes `M_ext≤B/λ`.
This entire connection is proved in Lean from the stated realization A002.

The general equality between the integrated differential form and the
closed form on noncompact functions remains a separate result; it is
neither asserted nor used as a hidden assumption of this transfer. A
classical proof by approximation in the graph norm and closure of the
covariant derivatives remains possible if a later step needs it.

### 4.4 From the second level to the inequality for all test functions

The spectral min-max principle gives, on the domain of the radial operator,

\[
 \operatorname{Re}\langle w,Hw\rangle\ge\Lambda_2\|w\|^2
 \quad(w\perp\phi).
\]

For a test function `u`, its L² class and the eigenvector `φ` both belong
to the domain. Write `u=⟨φ,u⟩φ+w`; the remainder therefore belongs to
this same domain. The eigenvalue equation and symmetry cancel the cross
terms in `Re⟨u,Hu⟩−Λ₁‖u‖²`. Since `φ` is normalized, this yields

\[
 \operatorname{Re}\langle u,Hu\rangle-\Lambda_1\|u\|^2
 \ge(\Lambda_2-\Lambda_1)
       (\|u\|^2-|\langle\phi,u\rangle|^2)
 \ge\gamma\lambda
       (\|u\|^2-|\langle\phi,u\rangle|^2).
\]

`MagneticIntegrationByParts` and `WavefunctionL2Bridge` identify the left-hand
side with `magneticForm … u−Λ₁ mass u`, since `u` is a test function.
No integral identity for the noncompact remainder is needed.
This justifies exactly the inequality in the `ground` field. The passage
from the two levels in the published result to the operator lower bound
above, together with the identification of conventions, constitutes the
informal proof of this field, included in the justification of A004.
These steps are not certified in Lean by the admitted declaration. No
estimate on the nonradial potential enters the argument.

## 5. Profile misprints that must not be carried over

In the checked PDF version, p. 11, the function described as normalized is written `h⁻¹ᐟ² ψₕ(√h x)`: the unitary factor in dimension two is `h⁺¹ᐟ²`. In (2.6), p. 10, the Gaussian also has a width incompatible with the operator (2.2). These profile formulas are not needed for the contract.

Independent check: for `−Δ+ν²|x|²` in dimension two, the normalized Gaussian is `√(ν/π) exp(−ν|x|²/2)`, with energy `2ν`. With the operator (2.2), `ν=√(1+4μ)/2`. The formula printed in (2.6) is indeed normalized, but its exponent is twice as large as it should be for this value of `ν`. The level approximation used above is consistent with the direct oscillator calculation; no incorrect profile constant is carried over.

## 6. Current boundary

A004 provides the witness of `RadialCoreSpectralData` for the explicit
core. Its justification distinguishes the harmonic approximation of the
first two levels, the min-max principle, changes of scale, and the
connections to the actual operator and `atomicGroundEnergy`, as well as
the separate real, radial, strictly positive choice. The admitted result
is this specialized classical corollary, not a literal citation of
Theorem 1.1 alone.

From this witness and A002, localization, the genuinely self-adjoint
compression, its inverse, the Schur root, the minimum, simplicity, and
the gap of the full potential are proved without any new admitted result.
Their assembly requires no form identity for the noncompact ground state.
The Agmon estimates already proved are separate consequences, outside this
contract. The passage from the actual state to its radial ODE, its
integrability with respect to `r dr`, its identification with the exterior
kernel, and the formulas in Γ are not added to the admitted result: they
are proved separately. The [source profiles](CUSP_SOURCE_PROFILES.md),
the [channels](ACTIVE_CHANNEL_ASYMPTOTIC.md), and the
[spectral transfer for the double well](GLOBAL_PARITY_DOUBLET.md)
are also established by analysis of the constructed potential. Their
[final assembly](../InfiniteZero/Remaining.lean) concludes `thm_main`
modulo A002–A005, without extending A004 to a tunneling estimate.
