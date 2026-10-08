# Classical admissions and the final proof

`thm_main` has a Lean proof with no `sorry` in its body.
The stronger theorem `elementaryPotential_main` literally fixes the
potential `elementaryParameters.potential` and constructs a threshold `L₀`
before any `L≥L₀`. **Three classical admissions A002–A004 remain among
its transitive dependencies**: these three classical results have not been
formalized from Lean's foundations alone.
Their contracts, references, and natural-language proofs are recorded below.

## Proof of the estimates for the constructed potential

The diagonal defect and both Schur corrections are proved to be `o(A)`
relative to the positive envelope of the same witnesses used in the hopping
asymptotic. The spectral results specific to the double well, source estimates,
and tunneling estimates are proved using the three classical admissions.

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
| Hopping | Actual complex integral, cosine with a positive envelope, continuous asymptotically linear phase and relative o(1) error, via A002–A004 |
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

## A003 — the standard Landau resolvent kernel

**Lean declaration:** `InfiniteZero.classical_standard_landau_resolvent`, in
[ClassicalLandauResolvent.lean](../InfiniteZero/ClassicalLandauResolvent.lean).

**Status:** one explicit `sorry` for the standard closed-operator kernel
identity at Planck constant one. The conversion to smooth solutions and
the semiclassical parameters is proved in Lean.

**Statement in natural language.** Let `B, ρ > 0` and let
`H_B = (−i∇−Bx⊥/2)²` be the closed free Landau operator on complex
`L²(ℝ²)`. For every vector `U` in its domain and every smooth compactly
supported source `f`, if `(H_B+ρ)U=[f]` in `L²`, then `U` is represented
almost everywhere by

\[
 x\longmapsto\int_{\mathbb R^2}K_{B,\rho}(x,y)f(y)\,dy,
\]

where, off the diagonal,

\[
 K_{B,\rho}(x,y)=e^{-iB(x\wedge y)/2}\frac{B}{4\pi}
 \int_0^\infty
 \frac{\exp[-\rho t-B\coth(Bt)|x-y|^2/4]}{\sinh(Bt)}\,dt.
\]

The exact contract is `HasStandardLandauResolvent`, in
[StandardLandauResolvent.lean](../InfiniteZero/StandardLandauResolvent.lean).
It uses the actual domain of `magneticOperator B 1 0` and the kernel
`freeLandauKernel B 1 ρ`. The value selected on the diagonal does not
affect the source integral.

**References.** Cornean–Fournais–Frank–Helffer, *Sharp trace asymptotics
for a class of 2D-magnetic operators*, Ann. Inst. Fourier **63** (2013),
[(B.21), p.2508](https://www.numdam.org/item/10.5802/aif.2835.pdf#page=53),
gives the heat kernel in the same symmetric gauge. The classical
Laplace-transform formula gives its resolvent at spectral parameter
`−ρ`; the article uses that transform on p.2509. Helffer–Pankrashkin,
*Semiclassical reduction for magnetic Schrödinger operator with periodic
zero-range potentials and applications*,
[(5.1)–(5.2), pp.11–12](https://arxiv.org/pdf/0802.1414#page=11),
gives the resolvent time-integral directly in Landau gauge.
The [natural-language proof](CLASSICAL_LANDAU_RESOLVENT.md) details the
phase convention, integrability, and almost-everywhere identification.
The heat-to-resolvent kernel identification remains the classical input.

**Proved reductions.**

- `MagneticInhomogeneousDomain` proves that a smooth `L²` function with
  an `L²` magnetic Hamiltonian belongs to the closed operator domain.
  Integration by parts gives an adjoint identity on tests, continuity
  extends it to the closed graph, and A002 supplies self-adjointness.
- `LandauResolventScaling` proves the proper-time substitution `τ=λt`,
  the phase identity, and the exact kernel and source-integral factors:
  `λ⁻² freeLandauKernel b λ⁻¹ E = freeLandauKernel (bλ) 1 (λ²E)`.
- `LandauResolventAssembly` combines these steps. The existing theorem
  `free_landau_resolvent_kernel` retains its statement and now has a
  proof from A002 and the reduced A003.

The atomic application remains proved in `LandauResolventBridge`:
magnetic covariance, support and smoothness of the physical source, the
resolvent equation, and its sign and scale. Atomic existence and
positivity of the energy shift are supplied by the separate spectral
analysis. A003 contains no atomic, cusp, separation, or tunneling estimate.

## A004 — the first two radial semiclassical levels

**Lean declaration:** `InfiniteZero.classical_radial_low_levels`, in
[ClassicalRadialLowLevels.lean](../InfiniteZero/ClassicalRadialLowLevels.lean).
Its `sorry` is explicit. The exact contract and correspondence with the
source are in [RADIAL_HARMONIC_CONTRACT.md](RADIAL_HARMONIC_CONTRACT.md).

**Statement in natural language.** Let `V` be a smooth, compactly supported,
nonpositive radial potential with a unique negative minimum at zero and
`d=V''(0)>0`. For sufficiently small `h>0`, the semiclassical magnetic
operator `Lₕ=(−ih∇−A)²+V` has a normalized ground eigenvector with a
smooth, real, radial, strictly positive representative. Its first two
operator-domain min-max levels `e₁(h),e₂(h)` satisfy

\[
 |e_j(h)-V(0)-h\mu_j|\le C h^{3/2},\qquad j=1,2,
\]

with a common `C>0` and a common upper bound on `h`. Here `μ₁,μ₂` are the
first two ordered values of the full oscillator mode family

\[
 \sqrt{1+2d}\,(2n+|m|+1)-m,
 \qquad n\in\mathbb N,\quad m\in\mathbb Z.
\]

The source identifies this mode family with the reference oscillator
spectrum. Its ordering and the subtraction of its first two values are
proved in Lean.

**Primary reference.** Helffer–Kachmar,
[arXiv:2208.13030v5](https://arxiv.org/pdf/2208.13030v5),
Theorem 1.1(1–2), Proposition 2.1, and Section 2.2, (2.2)–(2.4).
The hypotheses on the potential are (1.1). The remaining input is the
positive radial ground state and harmonic approximation in the source's
semiclassical convention.

**Proved deductions.** Lean converts the remainder bounds to limits,
computes `μ₁=√(1+2d)` and `μ₂=2√(1+2d)−1`, and obtains the positive
gap limit `δ=√(1+2d)−1`. The identity `Hₖ=k²L₁/ₖ` supplies the
large-coupling gap. A two-dimensional min-max argument proves the
operator lower bound on the orthogonal complement of the ground state;
this step is no longer admitted. The resulting
`classical_radial_harmonic` and `radial_core_spectral_data` are proved
assemblies using A004 and the unchanged realization input A002.

For the explicit core, Lean also proves the hypotheses for `V=p.core/b²`,
the exact change of field at coupling `bλ`, the common threshold, and the
rank-one test-function inequality. The estimate
`E°(λ)≤−λ²+Bλ`, for every `λ>0`, uses neither A004 nor A002.
See [RadialHarmonicAssembly.lean](../InfiniteZero/RadialHarmonicAssembly.lean),
[RadialCoreSpectralAssembly.lean](../InfiniteZero/RadialCoreSpectralAssembly.lean),
and [RadialCoreVariationalBound.lean](../InfiniteZero/RadialCoreVariationalBound.lean).

A004 contains no cusp, nonradial, source, hopping, or double-well estimate.
The actual radial ODE, exterior kernel and normalization bounds are
separate Lean proofs; see [RADIAL_NORMALIZATION.md](RADIAL_NORMALIZATION.md).

## Former A005 — point evaluation and elliptic estimates, now proved

There is no remaining admission in this block. The declaration
`classical_h2_point_evaluation` retains its name and statement and is
proved by `coordinateH2PointEvaluation` in
[CoordinatePointEvaluation.lean](../InfiniteZero/CoordinatePointEvaluation.lean).
It states that a constant independent of the smooth complex function `u`
satisfies

\[
 |u(0)|\le C\left(\int_{B_1}|u|^2
 +\sum_i\int_{B_1}|\partial_i u|^2
 +\sum_{i,j}\int_{B_1}|\partial_i\partial_j u|^2\right)^{1/2}.
\]

**Formalized proof.** Fix a smooth cutoff `χ` supported strictly inside
`B₁`, equal to one near zero, and put `v=χu`. Applying the fundamental
theorem of calculus in each coordinate gives

\[
 v(0)=\int_{[-1,0]^2}\partial_0\partial_1v.
\]

The boundary terms vanish by the support condition. Cauchy–Schwarz on
the unit-area square bounds this value by the `L²` norm of the mixed
derivative. That derivative is supported in `B₁`; the proved Sobolev
product estimate bounds it by the local `H²` norm of `u`. Cartesian
coordinate changes and the integral identities are checked in Lean.

Together with the proved uniform interior Sobolev estimate and the
higher-order embedding, this makes `classical_elliptic_sobolev_estimates`
and `classical_elliptic_interior_estimate` admission-free. Their existing
interfaces and applications to the magnetic equation are unchanged.
See the [elliptic proof](CLASSICAL_ELLIPTIC_INTERIOR.md) for the complete
argument and its connection to the classical Sobolev theorem.

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
