# Classical admissions and the final proof

`thm_main` has a Lean proof with no `sorry` in its body.
The stronger theorem `elementaryPotential_main` literally fixes the
potential `elementaryParameters.potential` and constructs a threshold `L₀`
before any `L≥L₀`. **Four classical admissions A002–A005 remain among
its transitive dependencies**: these four classical results have not been
formalized from Lean's foundations alone.
Their contracts, references, and natural-language proofs are recorded below.

## Proof of the estimates for the constructed potential

The diagonal defect and both Schur corrections are proved to be `o(A)`
relative to the positive envelope of the same witnesses used in the hopping
asymptotic. The spectral results specific to the double well, source estimates,
and tunneling estimates are proved using the four classical admissions.

The proof proceeds through
[ConstructedMainProof.lean](../InfiniteZero/ConstructedMainProof.lean),
then through `CuspParameters.mainConclusion` in
[Remaining.lean](../InfiniteZero/Remaining.lean). The former takes the
classical interfaces as explicit arguments and depends on no admission;
the latter instantiates them. `elementaryPotential_main` chooses the
verified elementary parameters, and `thm_main` derives the manuscript's
existential conclusion.

The proof constructs the channels and their asymptotic, the Schur errors,
then `LocalAnalyticData` and `OperatorMainConclusion` for the explicit potential.

| Block | Established result and scope |
|---|---|
| Fixed potential | `elementaryParameters_basicConditions` and admissibility, without admissions; existence of a separation certificate chosen before L |
| Atomic ground states | Existence, simplicity, gap, and core/full-potential comparison, via A002+A004; no nonradial data added to A004 |
| Sources and saddle | Exact radial tails, Γ≥c h², weighted forcing/response, jets, and L¹ norms; control of the physical incoming integral and seven inactive cells |
| Hopping | Actual complex integral, cosine with a positive envelope, continuous asymptotically linear phase and relative o(1) error, via A002–A005 |
| Two global modes | Self-adjoint parity restrictions, min/max min-max identities, physical spans, and gap above the ground eigenspace, via A002+A004 |
| Defect and Schur | Reconstruction on the opposite support, mass ≤C c²Γ² λ¹² exp(−2λ(G+J)), λ¹⁴ defect and λ¹⁵ correction; comparison with the same envelope and proved o(A) errors |
| Continuity and conclusion | Continuity of hopping and splitting, zero sequences, and alternating parity; final assembly for the explicitly fixed potential |

In the final comparison, the core and full-potential energies remain
distinct: `G=J(Ecore,R)` and `J=J(Efull,2L−R)`.
`UniversalComponentSourceL1` transfers the norms to every normalized
positive reference with its actual tail and every full ground state,
hence to the canonical state.
`PhysicalResidualMass` identifies the squared residual with `λ⁴` times
the actual mass on the opposite support; the Schur correction is bounded
by this square divided by `γλ/8`.
The reserve `2(G+J)−(2G+J)=J>0` absorbs the powers and the saddle cost.
`CanonicalParityRelativeErrors` preserves exactly the same `W.c` and `W.Γ`
as `CanonicalChannelAsymptotics`. See
[the mass estimates](OPPOSITE_SUPPORT_ESTIMATES.md) and
[the global doublet](GLOBAL_PARITY_DOUBLET.md).

The limits of the translation remain explicit in
[STATEMENT_AUDIT.md](STATEMENT_AUDIT.md) and
[MATHEMATICAL_SCOPE.md](MATHEMATICAL_SCOPE.md): no enumeration of the entire
spectrum, projection for a complete window, zero spacing or uniqueness,
or differentiated asymptotic expansion. These stronger statements are
not needed for the three conclusions of the active theorem.

## A002 — realization of the magnetic operator

**Lean declaration:** `InfiniteZero.magnetic_realization`, in
[`Remaining.lean`](../InfiniteZero/Remaining.lean).

**Status:** explicit `sorry`; a classical analytic interface independent
of the cusp potential and the tunneling phenomenon.

**Statement in natural language.** For every smooth, bounded real potential
and all real `b` and `λ`, the closure of the graph of the magnetic differential
expression on smooth, compactly supported functions is the graph of a
self-adjoint operator on the actual `L²` space. Its variational bottom
equals the infimum computed over test functions and supplies a lower
bound for its quadratic form on its entire domain. Its eigenspaces are
exactly the `L²` classes of smooth classical solutions, with the
corresponding canonical linear equivalence.

The precise contract is
[`IsMagneticRealization`](../InfiniteZero/OperatorBridge.lean). The operator
is **defined** by the concrete test graph and its closure, rather than
chosen arbitrarily within this contract. Density of the domain is deduced
in Lean from self-adjointness. The transfers of dimension and parity
from classical solutions to `L²` are proved.

This admission combines essential self-adjointness, the core property,
variational identification, and the global elliptic regularity needed
for the eigenspaces. It contains no assertion about crossings,
isolation of a doublet, dimension two, or a hopping asymptotic.

References and a mathematical proof of each field:
[classical operator realization](CLASSICAL_OPERATOR_REALIZATION.md).

## A003 — universal kernel of the free Landau resolvent

**Lean declaration:** `InfiniteZero.free_landau_resolvent_kernel`, in
[`Remaining.lean`](../InfiniteZero/Remaining.lean).

**Status:** one explicit `sorry`, restricted to a universal classical
identification. This admission contains no cusp potential, particular
atomic state, separation parameter, or tunneling estimate.

**Statement in natural language.** For all `b, λ, E > 0`, every smooth,
square-integrable complex function `u`, and every smooth, compactly
supported complex source `f`, the pointwise differential equation

\[
 (\texttt{magneticHamiltonian}(b,\lambda,0)+\lambda^2E)u=f
\]

implies, almost everywhere,

\[
 u(x)=\lambda^{-2}\int_{\mathbb R^2}
 \texttt{freeLandauKernel}(b,\lambda^{-1},E,x,y)f(y)\,dy.
\]

The exact contract is `FreeLandauResolventKernel`, in
[`LandauResolventBridge.lean`](../InfiniteZero/LandauResolventBridge.lean).
`HasPositiveLandauResolvent b` quantifies it over all strictly positive
couplings and energies. Assemblies with no admissions receive this
contract explicitly; the wrappers in `Remaining.lean` supply it through
A003. Thus `thm_main_variational_from_analytic_data` depends on A003 and
`thm_main_from_analytic_data` depends on A002 and A003. The final proof
`thm_main` constructs the original data and instantiates A002–A005.

**Precise primary reference.** H. D. Cornean, S. Fournais, R. L. Frank, and
B. Helffer, *Sharp trace asymptotics for a class of 2D-magnetic operators*,
Annales de l’Institut Fourier **63** (2013), equation **(B.21), p. 2508**,
[DOI 10.5802/aif.2835](https://doi.org/10.5802/aif.2835), followed by the
Laplace transform of the semigroup, also used on p. 2509. The publication
gives the heat kernel; the Lean contract is the resolvent corollary whose
scaling changes and domain argument are detailed in the
[natural-language proof](CLASSICAL_LANDAU_RESOLVENT.md).

Covariance of the magnetic derivatives and Hamiltonian, inversion, and
preservation of `L²` and mass are **proved** in
`MagneticCovariance.lean`. `LandauResolventBridge.lean` then proves that
the right-hand source is smooth and compactly supported, that the resolvent
equation has the required sign and scaling, and that A003 implies the
representation of the right state. Atomic existence, simplicity, and the
gap are deduced from A002 and A004. Positivity of the resolvent energy
is also proved at large coupling; `atomic_source_regime` assembles the
representation using A003. The derivatives and pointwise amplitudes of
the scattered source, followed by the hopping asymptotic, are proved
in their dedicated modules. A003 admits none of these estimates; the
relative spectral corrections are proved separately in `CanonicalParityRelativeErrors`.

`LandauExteriorConvolution` supplies continuity of the convolution
outside a ball containing the source support. The almost-everywhere
representation therefore becomes pointwise. `RadialCoreSourceRepresentation`
verifies the test source `−λ² core·φ`, its equation, and the exact cancellation
of the scaling factors. `RadialLandauAverage` and `RadialCoreNormalization`
deduce the polar formula and the real integral identity for the coefficient
Γ of the same state. The A003 contract is explicit in these theorems.
No positivity of the angular average or Green factorization is included
in the admission or assumed by this identity.

## A004 — spectral data for the radial core alone

**Lean declaration:** `InfiniteZero.radial_core_spectral_data`, in
[`Remaining.lean`](../InfiniteZero/Remaining.lean).

**Status:** explicit `sorry`; a classical corollary of magnetic harmonic
approximation for a radial single well. Classical extension audited on
18 September 2026: addition only of a real, radial, strictly positive
ground-state choice, at the same threshold. The natural-language proof
and checks of conventions appear in
[RADIAL_HARMONIC_CONTRACT.md](RADIAL_HARMONIC_CONTRACT.md).

**Exact statement.** For every `b>0` and `p.r₀>0`, an element of
`RadialCoreSpectralData b p` exists. Constants `γ,B,T>0` are chosen before
the coupling. For each `λ≥T`, the core `p.core` has a normalized smooth
L² ground state at `atomicGroundEnergy b p.core λ`. Its rescaled energy
`e=λ⁻² atomicGroundEnergy b p.core λ` satisfies `e≤−1+B/λ`,
and for every test function `u`:

```text
γ λ (mass u − ‖waveInner φ u‖²)
  ≤ magneticForm b λ p.core u − λ² e mass u.
```

A separate field, leaving `ground` unchanged, also requires:

```lean
positive_radial_ground : ∀ coupling, threshold ≤ coupling → ∃ φ,
  IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ
```

The predicate in [`RealRadialState.lean`](../InfiniteZero/RealRadialState.lean)
says exactly `φ x = (realRadialProfile φ ‖x‖ : ℂ)` and `0 < (φ x).re`
for every `x`, where `realRadialProfile φ r = (φ (r • coordinateVector 0)).re`.
The two existential fields may choose states with different phases.
Positivity of `canonicalAtomicState` does not follow automatically.
`RadialCoreSpectralData.positive_ground_with_gap`, in `RadialCoreGroundChoice`,
proves that a single positive choice satisfies both the energy and the gap
in the `ground` field: the gap extended to the graph through A002 forces
simplicity, and a unitary phase does not change the norm of the overlap.
This is a Lean consequence of the unchanged contract, not a new admission.

**Primary reference.** Helffer–Kachmar,
[arXiv:2208.13030v5](https://arxiv.org/pdf/2208.13030v5),
Theorem 1.1(1–2), p. 3, whose item (2) directly supplies the normalized
positive radial choice; Proposition 2.1, pp. 11–12, applied to the first two
min-max levels of the full operator; positivity of the oscillator gap,
p. 12; change of field in Remark 1.6, pp. 7–8.

**Natural-language proof.** The potential `p.core/b²` satisfies the radial
hypotheses (1.1). The exact identity
`Hλ=b²λ² L_(1/(bλ))^(p.core/b²)` turns the harmonic approximation into an
energy `−λ²+O(λ)` and a gap `≥γλ`. The classical realization A002 identifies
the operator, its variational ground energy, and its smooth representative.
For a test function, orthogonal decomposition along this ground state and
the second min-max level give the final inequality; the Hamiltonian–form
identity is used only on the compactly supported test function.
The constant and threshold are then enlarged to cover `λ≥T`.

For the new field, apply item (2) to the same potential `p.core/b²`
with `ε=1/(bλ)`. This positive multiplication of the operator changes
neither the eigenfunction nor its norm: no spatial dilation is needed.
If its threshold is `ε₀>0`, taking
`T ≥ max(T_ancien,1/(bε₀),1)` preserves the old and new fields
simultaneously. Almost-everywhere identification of the smooth representatives
becomes pointwise and preserves reality, radiality, and strict positivity.

**Boundary.** A004 says nothing about the cusps, the nonradial potential,
Agmon estimates, sources, hopping, or the double well. It assumes no
continuous phase for the state and gives no convergence of its profile.
The ODE for the actual state's profile, radial integrability for `r dr`,
identification with the exterior kernel, monotonicity of the profile,
its uniform bound on `[0,h]`, and the comparison `f≤ΓK` are separate
Lean connections, with no additional field in this admission.
The assembly of the bound `Γ≥c h²`, hence `Γ⁻¹≤C h⁻²`, compiles;
its proof uses A002+A004, without A003, and does not assume Lemma B.1.
The auxiliary convolution integral formula uses A003 separately.
See the [distinction and natural-language proof](RADIAL_NORMALIZATION.md).
The nonradial construction in `AtomicGroundConstruction` and exponential
comparison in `AtomicGroundComparison` are proved; their wrappers
`CuspParameters.eventual_atomicGround_properties`,
`atomicGroundEnergy_exponential_comparison`, and
`atomicGroundVectors_exponential_comparison` use exactly A002 and A004.
The wrapper `CuspParameters.atomic_source_regime` uses A002+A003+A004
and adds identification with the free kernel. The assemblies
`thm_main_*_from_analytic_data`, which already receive their atomic data,
retain their displayed A002/A003 dependencies.

## A005 — interior elliptic estimate on a fixed ball

**Lean declaration:** `InfiniteZero.classical_elliptic_interior_estimate`,
in [ClassicalEllipticInterior.lean](../InfiniteZero/ClassicalEllipticInterior.lean).
Its `sorry` is explicit. The precise contract is
`HasInteriorEllipticEstimate` in
[EllipticInteriorContract.lean](../InfiniteZero/EllipticInteriorContract.lean).

**Statement in natural language.** For every order `n` and bound `B≥0`,
there exists `C(n,B)>0`, chosen before the coefficients and functions,
such that: if `−Δu+a·∇u+qu=f` in `B(0,2)`, the functions are smooth and
complex-valued, and the jets of `a,q` through order `n` are bounded by
`B` on this ball, then the jets of `u` through order `n` at the center
are bounded by `C(U+F)`. Here `U²` bounds the local mass of `u`,
and `F²` bounds that of each unit-direction jet of `f` through order `n`.

This admission contains no magnetic parameter, cusp potential, weight,
coefficient Γ, or tunneling estimate. Its uniform constant comes from
the Poisson estimate and bounds on the lower-order terms;
no sign condition on `q` is required.

The [references and natural-language proof](CLASSICAL_ELLIPTIC_INTERIOR.md)
detail the complex-valued adaptation: Caccioppoli, the interior Poisson
estimate, commutators on nested balls, then Sobolev embedding in dimension
two. Hunter's notes, Theorems 4.27, 4.28, and 3.49, are cited as classical
ingredients, without attributing the precise contract variant to them.
The [connections to the actual potential](ATOMIC_RESPONSE_JETS.md) are
proved in Lean and receive A005 as an explicit hypothesis; only the
public wrapper instantiates it. They control the same Schur correction
without using A003.

## Estimates and constructions proved in Lean

- Positivity of the geometric phase coefficient is proved.
- Radial and energy derivatives, the eikonal equation, convexity,
  the integral representation, and identification of the action with
  the proper-time minimum are proved. The rate `h log K → −J` for the
  integral defining the kernel is proved uniformly in energy and radius
  on every strictly positive compact rectangle, at fixed field.
- The leading Laplace coefficient of this kernel is proved uniformly
  on every positive real compact set in `(E,r)`, at fixed field `b>0`:
  `h^(3/2) exp(J/h) K` tends to the explicit positive coefficient
  `landauLeadingCoefficient`. The relative form and the limit with
  moving parameters are proved; the differentiated expansion remains open.
  The integral at complex radius is defined, and its integrability is
  proved when `Re(r²)>0`. Its norm is bounded by the real kernel at radius
  `sqrt(Re(r²))`, with an exact norm identity for the integrands.
  The complex relative asymptotic is proved uniformly for
  `r+δ`, `|δ|≤M tStar h^(3/4)`, retaining `J(E,r)+J′(E,r)δ`
  in the exponent. Local domination, tails, and assembly of the actual
  integral are verified. Its holomorphy on `Re(r²)>0` and joint
  compositions at the three cusp radii are proved, with a common geometric
  bidisc. Profiles at the actual radii and the quadratic magnetic-phase
  remainder are also controlled on the active window. The incoming factors
  and exact integral change of variables are proved; their relative
  asymptotic integration and connection to hopping are proved,
  see [the active channels](ACTIVE_CHANNEL_ASYMPTOTIC.md).
- The core–cusp and core–core margins admit a choice of `L₀` uniform
  for `E>0` and `0<E₀≤2`, after the potential is fixed.
- The seven action margins are established on the entire closed supports,
  with the two energies kept distinct. The nine cell integrals converge
  absolutely for every continuous atomic function.
- Upper and lower bounds with arbitrarily small loss for the real log-flat
  integral are proved for `t^m`, `m : ℕ`, including `m=2` from the cusp
  Jacobian. The rate `log(I)/log²(1/h) → −β` is uniform on compact sets
  of positive slopes. The lower bound follows simply by integrating on
  `(h,2h)`: precise saddle localization is not needed for this rate alone.
  The pointwise majorant, exact kernel action, and compact support now
  give the actual weighted forcing at k=0 and the refined L² response,
  as detailed in [CUSP_FINE_FORCING.md](CUSP_FINE_FORCING.md).
  The extension to [forcing derivatives](CUSP_FORCING_DERIVATIVES.md)
  is also proved. The pointwise scattered sources, their L¹ norms,
  and their relative negligibility in the active cell are proved;
  see [ACTIVE_SCATTERED.md](ACTIVE_SCATTERED.md). The normal saddle model,
  complete incoming integral, and canonical connection are all assembled.
- The change of variables for the actual cusp in the Euclidean plane,
  with Jacobian `t²`, is proved. Reduction of
  `∫ |q₊| exp(−a t/h)` to the normal log-flat integral and tangential cutoff
  is exact; its upper bound follows from the preceding results without
  any eigenstate hypothesis.
- The large complex root of `w+Log w=L` is constructed by contraction,
  with uniqueness in `Re w≥2`. For `L=ℓ+d`, its expansion
  `w=ℓ−log ℓ+d+o(1)` is proved uniformly on `‖d‖≤M`.
  Its holomorphy and derivative are proved on the explicit domain.
  For the actual coefficient `c*tStar/h`, the critical identities,
  branches, logarithmic substitution, and contour deformation are proved.
  The nonzero complex leading term of the normal integral is
  established, including with the actual cutoff `p.χa` of the potential,
  at fixed parameters, for `m : ℕ` and `Re c>0`.
  The connector, left tail, and cutoff error are controlled after normalization.
  The phase of this leading term is continuous at large couplings
  and tends to zero after division by `λ`. The integral norm on the
  saddle contour remains bounded after normalization. A wider truncation,
  `tStar h^(3/4)`, preserves the leading term; its contour errors are
  exponentially small in `h^(-1/4)` and rigorously absorbed.
  The outer real tail is controlled uniformly over slopes `A≥A₀>0`.
  Every polynomial factor `h^(−N)` is absorbed, even under both normalizers.
  The absolute bound on the product of the restricted contours permits
  insertion of a multiplier uniformly close to a constant, once its
  integrability and that closeness have actually been established.
  See [the proofs and their limits](COMPLEX_SADDLE.md).
  The [full physical connection](INCOMING_PHYSICAL_ASYMPTOTIC.md),
  followed by assembly of the cell and channels, is proved separately.
- For this explicit action, the penalty at tips of the same cusp is
  at least `3bR²/4`, uniformly for every positive energy.
- Sign control at the appropriate phase values is proved.
- Intermediate values, infinitely many zeros, and strictly increasing
  sequences tending to infinity are proved.
- The two zero sequences are constructed separately.
- The passage from cells to the hopping cosine and from separate
  Schur errors to the splitting cosine is proved under the displayed hypotheses.
- The potential already satisfies global smoothness, the bound `[-1,0]`,
  compact support, nonradiality, and symmetry. The closed supports of the
  core and the two cusps are pairwise disjoint.
- It has a unique minimum at zero, and its second derivative in direction
  `u` equals `2 * ‖u‖² / r₀²`. None of these results depends on an admission.
- The elementary parameter conditions have an explicit witness;
  existence of an admissible cusp potential is proved without admissions.
- Invariance of hopping under a constant unitary phase is proved.
- The representation of the right state follows from the universal classical identification
  A003, with covariance, regularity, support, and scaling change proved.
- Dimensions two and one are deduced from mode decompositions,
  rather than admitted as numerical dimensions.
- Transfer of dimension and parity to the `L²` operator is proved.

## Automatic checks

`python3 scripts/update_status.py` inspects compiled dependencies and
transitive axioms. The audit fails if an unregistered admission appears
or contaminates the core declared to be proved. The standard axioms
`propext`, `Classical.choice`, and `Quot.sound` are not gaps in the
manuscript. `sorryAx`, by contrast, signals a missing proof.

See [the proved construction](CONSTRUCTION.md), [the exact inventory](STATUS.md),
and [the mathematical scope](MATHEMATICAL_SCOPE.md).
