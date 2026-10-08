# Infinite Zero — Lean formalization of `thm:main`

Lean 4.30.0 project / Mathlib pinned to commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

**Manuscript:** the [LaTeX article](article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex)
and its figures are in [article/](article/README.md), with compilation instructions.

**Review website:** [website/](website/README.md) provides side-by-side
reading of the manuscript and Lean, dependency exploration, and the three
admissions with their justifications.
Run: `cd website && npm ci && npm run dev` (Node.js ≥ 22.13).

**Status: `thm_main` is proved in Lean modulo three explicit classical
admissions. Its body contains no `sorry`.** The stronger result
`elementaryPotential_main` fixes the literal potential
`elementaryParameters.potential` before the separation and coupling.
The original source, saddle, hopping, and relative spectral-error estimates,
and the final assembly, are constructed in Lean.
The three classical admissions A002, A003, and A004 concern the
self-adjoint realization, the standard Landau resolvent kernel on the
closed operator domain, and spectral harmonic approximation for the first
two radial semiclassical levels. The domain and parameter conversions
for the resolvent are proved in Lean. The interior elliptic estimate and
Sobolev point evaluation are also proved, without an additional admission.
Their precise references and natural-language proofs are documented.

The elementary potential construction is verified: global smoothness of
the cusps, compact support, values in `[-1,0]`, nonradiality, symmetry, a
unique minimum, and a positive second derivative at the minimum. Explicit
parameters yield an admissible potential without `sorry`.
The sharp action and log-flat bounds are established for the full right-hand
side of the correction PDE, its derivatives of every fixed order in local
L², the correction itself in global weighted L², and its pointwise jets on a
fixed neighborhood of the cusps, using the proved interior estimate.
The scattered source `λ²Wη` and all its jets up to a fixed maximum order
retain both local and global log-flat factors, with the same `cΓ` and a
polynomial cost `λ⁶`.
The incoming source also has its local profile with exact action and
polynomial cost `λ^(n+4)`; both bounds are assembled for the same states.
The [exact normalization of the incoming density and its uniform complex
profile](docs/INCOMING_MULTIPLIER.md) are proved at the actual core and full
potential energies. The profile is holomorphic on a common bidisk; its
integrated error on the normalized saddle contour tends to zero. Fubini,
integrability of the normal fibers, and positivity of the tangential
coefficient are also proved. The [connection to the physical incoming
integral](docs/INCOMING_PHYSICAL_ASYMPTOTIC.md) assembles the real truncation,
both deformations, and the exact logarithmic substitutions. Its normalized
complex limit is the nonzero `tStar⁶ (π/β) Bs²`, at the actual energies.
The [connection to the canonical channels and hopping](docs/ACTIVE_CHANNEL_ASYMPTOTIC.md)
is proved: negative sign, factor λ⁶√λ, explicit positive amplitude,
continuous phase with slope Φ*, and relative error o(1). The atomic
witnesses are shared by the active and inactive contributions.
The diagonal defect and both Schur corrections are `o(A)` for this same
envelope, in `CanonicalParityRelativeErrors`.
[Continuity of canonical hopping](docs/DILATION_AND_CONTINUITY.md) is proved
on a half-line, with the threshold chosen before any separation `L`, under
explicit radial data and realizations. This theorem has no admission;
the compiled wrapper `canonicalHopping_continuous hp` instantiates it from
`BasicConditions` using A002+A004 only.
The [overlap and parity trial states](docs/OVERLAP_AND_PARITY_TRIALS.md) are
controlled: `|canonicalOverlap| ≤ (C/λ) exp(−dλ)`, with common constants and
threshold for all `L≥4r₀`. The canonical even and odd trial states are
normalized, orthogonal, and independent. The translated-state residuals
and membership in the double-well domain are proved.
The [spectral construction in each parity sector](docs/PARITY_SPECTRAL_CONSTRUCTION.md)
provides genuine self-adjoint restrictions, coercivity on each trial
state's complement, and a Schur construction in each sector.
`DoubleWellParityGround` constructs these actual modes for the explicit
potential, with sectorial simplicity, energy exactly `parityEnergy`, and a
common lower bound `Eatom+hRad.gap·λ/4` on their complements. The threshold
precedes λ and L; `doubleWell_parityGrounds hp cert` instantiates only
A002+A004. The [parity energies and their difference](docs/DILATION_AND_CONTINUITY.md)
are continuous at every positive coupling. The [first two global min-max
values](docs/GLOBAL_PARITY_DOUBLET.md) are exactly the minimum and maximum
of these energies: `doubleWell_global_minmax hp cert` proves this using
A002+A004, with a threshold preceding λ and L. The global eigenspaces have
normalized physical decompositions into one mode, or two at a crossing,
with a positive gap. The sectorial correction is controlled by the squared
actual residual divided by `hRad.gap·λ/8`; its smallness relative to the
tunneling envelope is proved through reconstruction on the opposite support
and an action margin. The compiled wrapper
`doubleWell_twoModeRealization hp cert` directly supplies the modes of
`TwoModeRealization`; `doubleWell_spectral_realization hp cert` then gives
`SpectralRealization`. Both retain the actual global gap and a threshold
preceding L, using A002+A004 only.
[Coercivity on their complement](docs/TWO_WELL_COERCIVITY.md) is proved on
the actual operator domain: the energy is bounded below by `Eatom + cλ`,
with `c>0` and a common threshold for every admissible separation. It
follows from the atomic gap, an IMS partition around the full supports,
and tail control. Its only classical inputs are A002 and A004.
The final proof chooses `elementaryParameters`, with `r₀=1`, `R=16`,
`b=1`, `ε=1/16`, `a=β=tStar=s₀=1`, and `t₀=1/100`, and the two explicit
smooth cutoffs from `ConstructionParameters`. A separation certificate is
then constructed. `elementaryPotential_main` gives all three conclusions
for this same potential and every `L≥L₀`; no existence of suitable analytic
data is added to the hypotheses of `thm_main`.
See the [exact statement audit](docs/STATEMENT_AUDIT.md).

The ground state of the actual potential is **constructed, simple, and
isolated by a coercive gap** at large coupling, modulo A002 and A004:
`CuspParameters.eventual_atomicGround_properties` requires only
`BasicConditions`. A004 supplies a positive normalized radial ground state
and harmonic-approximation error bounds for the first two semiclassical
levels of a general radial well. Lean proves the oscillator-level ordering,
the large-coupling gap limit, and the min-max inequality on the orthogonal
complement. `RadialCoreSpectralAssembly` applies these results to the
explicit core using A002; field conversion, the uniform test gap, and the
energy upper bound are also proved. `AtomicGroundConstruction`
then proves the passage to the full potential, with its actual domains
and Schur compression; no nonradial ground state or gap is admitted.
The certificate retains a gap `hRad.gap / 2 * coupling` for the unscaled
operator. `AtomicGroundEnergyBounds` also proves `scaledAtomicEnergy → 1`
and eventual membership in `[1/2,1]`. Modulo A002+A003+A004, the wrapper
`CuspParameters.atomic_source_regime` supplies a common threshold independent
of `L`: the canonical state is an actual ground state, its resolvent
representation holds for every `L`, and the nine cells are integrable when
`R<2L`. The source identity and reality of hopping follow. The corresponding
conditional modules contain no `sorry` and take the classical interfaces
as explicit arguments.

An [absolute global Agmon bound](docs/AGMON_DECAY.md) is proved in
[AtomicAgmonGlobal.lean](InfiniteZero/AtomicAgmonGlobal.lean) for the core
and full potential: for `λ>0`, every normalized eigenstate with energy
`E≤−3λ²/4` satisfies `∫_{‖x‖≥4r₀}|φ|²≤(C/λ²)exp(−2dλ)`, with `C,d>0`
chosen before `λ`. The weight is smooth and bounded; spatial cutoffs are
removed by L² dominated convergence, without assuming global energy
integrability. `AtomicGroundAgmon` applies this bound to ground states at
large coupling; `CuspParameters.canonicalAtomicState_agmon_tail` requires
only `BasicConditions`, modulo A002+A004, and also establishes that the
canonical state is a ground state.
The [exponential core/full-potential comparison](docs/ATOMIC_COMPARISON.md)
is proved in `AtomicGroundComparison`:
`0≤Ecore−Efull≤C exp(−dλ)`, and actual normalized ground vectors `u,v` can
be chosen with `‖v−u‖₂≤C exp(−dλ)` and strictly positive real overlap.
The constants and threshold precede `λ`. The wrappers
`CuspParameters.atomicGroundEnergy_exponential_comparison` and
`CuspParameters.atomicGroundVectors_exponential_comparison` require only
`BasicConditions`, modulo A002+A004. This choice fixes the relative phase
of the compared vectors; it does not impose a phase on the canonical
states. Pointwise estimates and source amplitudes follow from the steps
below. The asymptotic of the full active cell is proved. The actual
sectorial double-well modes are also constructed and identified with the
first two global min-max values; relative control of the defect and
spectral corrections is proved as well.

The [weighted inverse for the exact cusp weight](docs/CUSP_WEIGHTED_INVERSE.md)
is constructed in `AtomicCuspWeightedInverse` from the same explicit
classical interfaces. For every energy `E≤Ecore`, the norm of the actual
operator `exp(κλT) ι (A_Q−E)⁻¹ Q exp(−κλT)` is at most `12/(γλ)`.
The constants precede `λ`, the radial reference precedes `E` and `κ`, and
the resolvent precedes `κ`. The weight is Lipschitz and agrees with the
normal coordinate on the closed cusp supports. The proof uses smooth
weights, graph closure, and a strong limit; it does not assume preservation
of the domain by the weight. The covered half-line includes `Efull≤Ecore`;
the part of the TeX window above `Ecore` is not claimed. The connection to
pointwise source estimates is described below.

The [weighted response of the actual ground state](docs/ATOMIC_WEIGHTED_RESPONSE.md)
is assembled in `AtomicGroundWeightedResponse` and
`AtomicGroundWeightedDecay`. The reference is the same **positive radial**
ground state, carrying the initial gap through `RadialCoreGroundChoice`,
and the full vector comes from its own Schur root. For `η=v−cu`,
`W=p.potential−p.core`, and `Mκ=exp(κλT)`, the exact retained bound is
`‖Mκ η‖₂≤(12cλ/γ)‖Mκ Wu‖₂`. The actual residual and Agmon then give
`‖Mκ η‖₂≤C exp(−dλ)` and `c∈[1/2,1]`. The constants precede `λ`; the
states and `c` precede `κ`. The response equation is proved in the actual
operator domain. `AtomicGroundWeightedDecomposition` recovers the same
actual wavefunctions, orthogonality of the correction, its weighted mass,
and its pointwise differential equation. The wrapper
`CuspParameters.atomicGround_weighted_decomposition` requires only
`BasicConditions`, modulo A002+A004.

The [sharp cusp estimates](docs/CUSP_FINE_FORCING.md) apply the exact tail
of the same radial state: the forcing satisfies
`‖Mκ Wφcore‖₂≤CΓ h⁻² exp(−J(Ecore,h,R)/h−β₁log²(1/h))` for every
`0<β₁<β`. The same correction satisfies the bound
`CcΓ h⁻³ exp(−J(Ecore,h,R)/h−β₁log²(1/h))`. The action is preserved
exactly; the polynomial cost suffices for statements allowing an unspecified
power. `AtomicEnergyShiftForcing` also bounds the semiclassical energy shift
by `3‖MκWφcore‖₂`, with a single forcing factor.
The [forcing derivatives](docs/CUSP_FORCING_DERIVATIVES.md) retain the same
envelope for every fixed maximum order: Cauchy on disks of radius h,
log-flat margins for the actual cusp jets, Leibniz, and compact support
give pointwise and then L² control.
`radialCore_fine_forcing_derivatives` applies this to actual core states,
with a common constant, threshold, and coefficient Γ for the required
orders, using A002+A004 only.
The [full correction PDE data](docs/ATOMIC_FINE_RESPONSE_DATA.md) are
assembled: the energy-shift term also retains a single factor `cΓ`, using
the [normalized radial jets](docs/RADIAL_WEIGHTED_JETS.md).
`atomicGround_fine_response_data` supplies the same wavefunctions, the exact
PDE, the sharp correction mass, and local L² norms of every required
derivative of the right-hand side. It requires only `BasicConditions`,
`0<β₁<β`, and the maximum order, using A002+A004.
The [passage to pointwise correction jets](docs/ATOMIC_RESPONSE_JETS.md) is
assembled in `atomicGround_fine_response_jets`: the same state, cΓ, action,
and log-flat coefficient, with polynomial cost λ⁴. Lean proves point
evaluation by the H² norm using a fixed cutoff, the fundamental theorem
of calculus on a rectangle, and Cauchy–Schwarz. Cutoff energy estimates
and induction give the interior estimate uniformly in bounded coefficient
jets. Higher-order point bounds, source and tensor norm conversions, and
all changes of scale are proved as well.
The [scattered-source profile](docs/CUSP_SCATTERED_SOURCE.md) is assembled
by Leibniz for these same states: `atomicGround_scattered_source_jets`
simultaneously retains `exp(−βglobal log²λ)` and `logFlat βlocal tStar t`,
for two independent margins in `(0,β)`, together with `exp(−κλt)`.
The constants precede λ; the states precede κ, the jets, and the points
of both closed supports. This step adds no admission.
The [simultaneous profiles](docs/CUSP_SOURCE_PROFILES.md), in
`atomicGround_source_profiles`, also control the incoming source on both
cusps, with action `J(Ecore,R)+t/8` and power `λ^(n+4)`. The three log-flat
margins can be chosen independently before λ.
[L¹ integration of these profiles](docs/CUSP_SOURCE_L1.md) is proved with
the actual Jacobian t² and transverse factor 2s₀.
`atomicGround_source_L1` keeps the incoming and scattered costs separate;
`atomicGround_component_source_L1` bounds both full cusp components by
`CΓλ⁶exp(−λJ−β₁log²λ)` for every `0<β₁<β`, and the core component by
`Ccoreλ²`, for the same full state.

The [seven inactive cells](docs/INACTIVE_CELLS.md) each have an absolute
bound `C(Γ²+1)λ¹⁰exp(−λ(Aref+31δhop))`, for the actual ground state and
for the canonical state. `atomicGround_inactive_cells` supplies the
physical connection through A002+A004, without requiring a source
hypothesis. The action retains the core energy in both tails and the full
energy in the bridge. The canonical phase is handled by exact cell
invariance; the positive radial decomposition is unchanged. Polynomial
control of the normalization quotient and absorption of the inverse square
of the scalar saddle envelope yield the seven relative bounds, and their
summed norms: `C * activeSaddleTexEnvelope * exp(−15δhop λ)`.
`atomicGround_inactive_relative_tex` retains the same states and coefficients.
The comparison between the Gaussian prefactors `Re w` and `1+w` is proved,
with their squared ratio tending to one. The envelope is explicitly defined
and identified with the active cell's leading term, with the fixed positive
coefficient `activeTangentialLeadingCoefficient`.
The version `canonical_inactive_relative_tex` holds for every normalized
positive radial state and its own Γ, then every `c≥1/2`: uniqueness of
these states and tails allows reuse of the active proof's witnesses.
The [exact incoming-source formula](docs/INCOMING_SOURCE_FORMULA.md) is
connected to the three complex kernels in the physical charts, preserving
core/core/full energies, cutoffs, and magnetic phase. The change of variables
for this incoming cell is exact, with Jacobians t²u² and outer factor −h².
The [reduction to the incoming part](docs/ACTIVE_SCATTERED.md) also controls
the three contributions containing the scattered correction:
`atomicGround_active_incoming_reduction` gives, for the same states and cΓ,
`‖full cell − incoming cell‖ ≤ C * envelopeTex * exp(−(β/8)log²λ)`.
The canonical cell satisfies the same bound. The only arguments are the
elementary potential conditions and `R<2L`, modulo A002+A004;
the incoming asymptotic is assembled in `IncomingCellTexAsymptotic`.
`CanonicalChannelAsymptotics` constructs the channels and then the cosine
formula for actual hopping, with amplitude 2a. The classical wrappers
require only `BasicConditions` and the constructed geometric separation;
they admit no tunneling estimate.

The [exterior radial block](docs/RADIAL_EXTERIOR_KERNEL.md) proves the ODE
for the actual Landau integral kernel, its membership in `L²((a,∞),r dr)`,
and uniqueness of the real exterior `L²` branch: every solution of this ODE
is `Γ K`, with `Γ>0` if positive. Derivative energy is deduced from
Caccioppoli and the Wronskian is then shown to vanish; that energy is not
assumed. The connection to the actual core state is established:
`RadialCoreExteriorState` derives the exact identity for the actual
normalized state. A004 and the realization A002 supply the classical
positive radial choice through `RadialCoreSpectralAssembly`; `MagneticRadialReduction` and `RadialPlaneL2`
prove the other two steps. The full ODE, decrease of the real profile,
and a uniform bound `f(r)≥c>0` on `[0,h]` are proved without pointwise
harmonic convergence. Wronskian comparison gives `f(r)≤ΓK(r)` for every
`r>0`. The compiled [normalization argument](docs/RADIAL_NORMALIZATION.md)
deduces `Γ≥c h²` and `Γ⁻¹≤C h⁻²`, modulo A002+A004 only. This power,
weaker than the TeX's `h^(3/2)`, suffices for polynomial losses under strict
exponential margins; Lemma B.1 and the literal manuscript bound are not
claimed. Auxiliary convolution and angular-average identities are also
compiled, with the free-kernel interface as an explicit argument for the
physical representation. This interface follows from A002+A003; these identities
are not needed for the Wronskian lower bound on Γ.
The complete radial-block checks passed: compilation, guards against
unauthorized admissions, and dependency export.

- [Statement and conditional proof](InfiniteZero/Main.lean):
  `thm_main_of_analytic_data`.
- [Conditional unbounded-operator version](InfiniteZero/OperatorMain.lean):
  `thm_main_operator_of_analytic_data`.
- [Final theorem and explicitly fixed potential](InfiniteZero/Remaining.lean):
  `elementaryPotential_main`, then `thm_main : ConstructedPotentialMainTheorem`,
  with no analytic argument or direct `sorry`; classical dependencies A002–A004.
- [Assembly without further admissions](InfiniteZero/ConstructedMainProof.lean):
  `operatorMainConclusion_of_radialData`, with all four analytic interfaces explicit, including the proved interior estimate.
- [Physical defects and action margin](docs/OPPOSITE_SUPPORT_ESTIMATES.md).
- [Admissions for human review](docs/ADMISSIONS.md).
- [Automatically verified inventory](docs/STATUS.md).
- [Correspondence with blueprint sublemmas](docs/BLUEPRINT_INDEX.md).
- [Dependency graph](docs/DEPENDENCIES.md).
- [Mathematical scope and modeling choices](docs/MATHEMATICAL_SCOPE.md).
- [Details of the proved construction](docs/CONSTRUCTION.md).
- [Proved real-action calculations](docs/REAL_ACTION.md).
- [Complex saddle: proofs and limitations](docs/COMPLEX_SADDLE.md).
- [Complex kernel on the active window: proof and scope](docs/SHRINKING_COMPLEX_KERNEL_PLAN.md).
- [Atomic-block proofs](docs/ATOMIC_PROOF_PLAN.md).
- [Global Agmon decay: proof and scope](docs/AGMON_DECAY.md).
- [Exponential atomic comparison: energy, L² norm, and phase](docs/ATOMIC_COMPARISON.md).
- [Weighted cusp inverse: proof and energy range](docs/CUSP_WEIGHTED_INVERSE.md).
- [Weighted atomic response: same positive state, equation, and absolute decay](docs/ATOMIC_WEIGHTED_RESPONSE.md).
- [Cusp forcing and weighted response: exact action and log-flat factor](docs/CUSP_FINE_FORCING.md).
- [Forcing derivatives: same radial state, coefficient, and global bound](docs/CUSP_FORCING_DERIVATIVES.md).
- [Normalized radial jets: weighted bounds without an extra Γ factor](docs/RADIAL_WEIGHTED_JETS.md).
- [Correction PDE: full right-hand side, same states, and local L² norms](docs/ATOMIC_FINE_RESPONSE_DATA.md).
- [Pointwise correction jets: rescaling and sharp bound](docs/ATOMIC_RESPONSE_JETS.md).
- [Proved Sobolev point evaluation and interior elliptic estimates](docs/CLASSICAL_ELLIPTIC_INTERIOR.md).
- [Exterior radial kernel: ODE, integrability, and uniqueness](docs/RADIAL_EXTERIOR_KERNEL.md).
- [Radial normalization: the Γ ≥ c h² variant and its exact scope](docs/RADIAL_NORMALIZATION.md).
- [Classical radial admission A004, references, and natural-language proof](docs/RADIAL_HARMONIC_CONTRACT.md).

## Verification

Run the full checks and regenerate the inventories with
`bash scripts/check.sh`. For initial setup:

```sh
lake update                  # initial setup only
lake exe cache get           # if compiled Mathlib files are missing
lake build
lake build InfiniteZero.Verification
python3 scripts/update_status.py
```

`lake-manifest.json` also locks transitive dependencies.
`Verification.lean` guards modules without admissions and separately checks
the permitted classical contracts. The audit inspects Lean's actual
transitive axioms; the absence of `sorry` in the body of `thm_main` does not
remove its three classical dependencies.

## Organization

| Module | Role |
|---|---|
| `MagneticModel` | Differential Hamiltonian, magnetic form, min-max values, eigenfunctions, and concrete hopping |
| `Construction` | Explicit core and cusp formulas; potential fixed before `L` and coupling |
| `ConstructionNonradial` | Proof that the explicit potential is nonradial |
| `ConstructionCompact` | Proof that the explicit potential has compact support |
| `ConstructionCoreSmooth`, `LogFlat`, `LogFlatSmooth`, `CuspKernelSmooth`, `ConstructionSmooth` | Smoothness of the core and of the cusps extended by zero |
| `ConstructionSupportSeparation`, `ConstructionMinimum` | Disjoint closed supports, unique minimum, and directional second derivative |
| `ConstructionParameters`, `ConstructionExistence` | Explicit parameters and admission-free existence of an admissible potential |
| `Geometry` | Distances, frames, magnetic phase, and positivity |
| `BridgeAction`, `GeometryAction` | Differentiation of the explicit action, convexity, and channel gap at the tips |
| `Oscillation` | Cosine asymptotics, signs, intermediate values, and divergent sequences |
| `LinearPhase` | Phase growth from its positive geometric slope |
| `SpectralAssembly` | Control relative to the positive envelope and exact splitting zeros |
| `GroundSpaceAlgebra` | Dimensions and parities from mode decompositions |
| `L2ParitySectors`, `DoubleWellInversionGraph`, `DoubleWellParityGraph`, `ReducingSubspaceRestriction`, `DoubleWellParityOperator` | Closed sectors, projections (I±J)/2, invariance of the actual graph, and self-adjoint restrictions with exact domain and action |
| `ParityTrialL2`, `AtomicTranslatedOverlap`, `ParityTrialCoercivity` | Sectorial orthogonality to the trial state implies orthogonality to both atoms; lower bound Eatom+hRad.gap·λ/4, threshold before L |
| `MagneticParityGraphLowerBound`, `MagneticParityNormalization`, `ParityEnergyIdentification` | Closure of the parity test graph, existence of normalized tests, and exact identification of parityEnergy with a lowest sectorial eigenvalue |
| `ParityGroundCertificate`, `ParitySchurGroundConstruction`, `EigenvectorComplementBound`, `ParityTrialEnergyBound`, `DoubleWellParityGround` | Actual modes of the constructed potential at parityEnergy; sectorial simplicity, gap ≥hRad.gap·λ/8, and absolute lower bound Eatom+hRad.gap·λ/4 on their complements, threshold before λ and L |
| `ClassicalDoubleWellParityGround` | From BasicConditions and separation: actual sectorial certificates, continuity of parityEnergy and signedSplitting at positive couplings; A002+A004 only |
| `ParityOperatorDecomposition`, `SecondEnergyParityUpper`, `SecondEnergyComplementLower`, `ParityGlobalMinmax`, `ConstructedGlobalMinmax`, `ClassicalGlobalMinmax` | Exact decomposition of the actual domain and global min-max values = min/max of sectorial bottoms; wrapper doubleWell_global_minmax under hp+cert, A002+A004 |
| `ParityGroundEigenspaces`, `ParityGlobalGroundGap`, `PhysicalEigenmodeTransfer`, `PhysicalParityModes` | Global eigenspaces with exactly one/two modes; normalized eigenfunctions and pointwise decompositions, positive gap even at crossings |
| `ParityTrialRayleigh`, `ParitySchurEnergyShift`, `ConstructedParitySchurEnergyBound` | Exact physical Rayleigh value Eatom+(δ±Reρ)/(1±s), then sectorial correction between zero and residual²/(hRad.gap·λ/8); physical connection to o(envelope) errors in CanonicalParityRelativeErrors |
| `ParityDoubletRealization`, `ConstructedDoubleWellSpectral`, `ClassicalDoubleWellSpectral` | TwoModeRealization then SpectralRealization and global gap for the explicit potential; doubleWell_spectral_realization hp cert, threshold before L, A002+A004 |
| `HoppingPhase` | Independence of the coefficient from the atomic state's phase |
| `MagneticDilationL2`, `UnitPhaseDistance`, `AtomicGroundDilationComparison`, `HoppingContinuity` | Comparison of actual dilated ground states modulo phase, bilinear bound, and continuity of canonical hopping on a half-line; threshold before L, explicit radial data and realizations, no admission in these theorems |
| `ClassicalHoppingContinuity` | canonicalHopping_continuous hp: the same complex continuity with threshold before L, using A002+A004 only; no continuous phase choice assumed |
| `MagneticCovariance`, `LandauResolventBridge` | Covariance, inversion, L², and normalization proved; right-state representation derived from the universal free-kernel contract, supplied by A002+A003 |
| `MagneticIMS`, `MagneticIMSIntegrated` | Pointwise IMS identity, then integrated on test functions; integrability deduced and coercive consequences transferred to the operator domain by graph closure |
| `MagneticIntegrationByParts` | Coordinate integration by parts, symmetry of covariant derivatives, and exact Hamiltonian–form identity on actual tests |
| `MagneticIntegrationByPartsLocal`, `MagneticLocalEnergy`, `MagneticAgmonLocal`, `MagneticAgmonWeighted` | Energy identity for actual eigenfunctions with compact cutoff; integrated inequality with weight exp(F), all integrability deduced |
| `AtomicAgmonRegion` | Eventual spectral margin λ²/4 outside the core and local estimate for cutoff eigenfunctions, even when the cutoff intersects a cusp |
| `SmoothExhaustionCutoffs`, `EigenfunctionCutoffLimits`, `MagneticAgmonBounded`, `AtomicAgmonWeight`, `AtomicAgmonGlobal` | Cutoff removal by dominated convergence, concrete smooth bounded weight, and absolute L² tail `(C/λ²)exp(−2dλ)` for `‖x‖≥4r₀`, for the core and full potential under `E≤−3λ²/4` |
| `AtomicGroundAgmon`, `AtomicPerturbationTail` | Tail of actual ground states at large coupling under radial data; squared norm of the concrete multiplier and residual controlled by exterior mass |
| `MagneticTestGraph`, `WavefunctionL2Bridge`, `MagneticGraphLowerBound` | Linearity of the test graph, identity of its closure, inner products and masses of L² representatives; transfer of rank-one bounds to the actual operator domain |
| `AtomicLocalizationCutoffs`, `AtomicLocalizationOverlap`, `AtomicLocalizationEnergy` | Fixed partition separating core and cusps, bounded IMS error, orthogonality defect controlled by exterior mass, exterior mass controlled by core energy |
| `AtomicLocalizationForms`, `AtomicLocalizationRankOne`, `AtomicLocalizationOperator`, `AtomicSpectralCoercivity` | Explicit radial data imply full-potential coercivity on tests and then on the closed operator domain, uniform threshold; spectral version without noncompact form-integrability assumptions |
| `MagneticBoundedPerturbation`, `AtomicPerturbationDomain`, `AtomicPerturbationSign` | Bounded self-adjoint nonpositive multiplication for the actual perturbation, transport of closed graphs, identical domains, and Rayleigh bound for the radial eigenvector |
| `LinearPMapBoundedPerturbation`, `OrthogonalCompression` | Sum with a bounded self-adjoint operator and actual self-adjoint orthogonal compression on its explicit domain |
| `CoerciveOperator`, `OperatorResolvent`, `CoerciveResolvent` | Bounded positive self-adjoint coercive inverse; actual resolvents, uniform bound, and continuity in energy |
| `SchurScalarRoot`, `SchurEigenvector`, `SchurGroundExistence`, `SchurGroundState` | Construction of a scalar root, reconstruction of an eigenvector in the actual domain, global minimum, and gap from complement coercivity and a trial vector |
| `SchurGroundEstimates`, `SchurResidualBounds`, `SchurGroundQuantitative` | Correction, energy, and normalization bounds; certificate and correction from the same root, coupling and diagonal controlled by the actual residual |
| `AtomicResidualDecay`, `AtomicSchurReference`, `SchurNormalizedComparison`, `AtomicGroundComparison` | Exponentially small residual; exponential comparison of actual energies and normalized L² ground vectors with fixed relative phase, under explicit radial data and realizations |
| `CuspWeight`, `SmoothPositivePart`, `CuspWeightApproximation` | Exact Lipschitz cusp weight and smooth approximations with uniformly bounded height and gradient |
| `MagneticWeightedTest`, `AtomicWeightedTestCoercivity`, `AtomicSmoothWeightedGraph`, `AtomicCuspWeightedGraph` | Exact weighted identity on tests, IMS absorption, graph closure, and strong limit to the exact weight |
| `AtomicWeightedTail`, `AtomicExponentialWeightOps`, `WeightedCompression`, `WeightedCompressedEstimate`, `AtomicCuspWeightedInverse` | Exponentially small weighted defect, exact lifting with residual, absorption, and actual conjugated compressed inverse with projection, norm ≤12/(γλ) for E≤Ecore |
| `RadialCoreGroundChoice`, `WeightedSchurCorrection`, `SchurResponseEquation` | Radial gap transferred to the positive choice; same Schur correction, weighted resolvent identity, and exact equation in the full domain |
| `AtomicWeightedResidual`, `SchurNormalizationThreshold`, `AtomicGroundWeightedResponse`, `AtomicGroundWeightedDecay` | Actual weighted forcing, response bound retaining c, absolute weighted L² decay, and c∈[1/2,1], with states chosen before κ |
| `AtomicResponseWavefunction`, `WeightedWavefunctionL2`, `AtomicGroundWeightedDecomposition` | Same actual wavefunctions, orthogonal correction, exponentially small weighted mass, and exact pointwise PDE |
| `LandauKernelExactActionUpper`, `CuspWeightedActionGain`, `RadialCoreEnergyBounds` | Kernel bound without action loss, weighted normal gain, and effective core energy in [1/2,1] |
| `CuspFineForcingPointwise`, `GenericCompactL2Bound`, `AtomicCuspFineForcing` | Actual undifferentiated forcing: bound Γh⁻²exp(−J/h−β₁log²(1/h)), pointwise then in actual L² |
| `LogFlatDerivativeLoss`, `CuspKernelJetBounds`, `ConstructionCuspJetBounds` | All actual cusp jets retain any strictly smaller log-flat coefficient, including at the tips |
| `ComplexLandauSmallDisk`, `ComplexLandauDerivativeBounds`, `RadialCompositionJetBounds`, `LandauSpatialDerivativeBounds`, `ExteriorRadialJetBounds` | Cauchy at radius h, exact action at every order, and identification of jets of the same tail ΓK |
| `SemiclassicalLeibniz`, `LogFlatWeightedAction`, `CuspFineForcingJets`, `AtomicCuspFineForcingDerivatives` | Semiclassical derivatives of the actual Wφ: weight after differentiation, pointwise envelope, and sharp mass bound |
| `GenericFiniteL2Bound`, `RadialCoreFineForcingDerivatives`, `ClassicalCuspForcingDerivatives` | Same energy and Γ of the actual core for every required order; sums of norms and wrapper through A002+A004 |
| `LipschitzExponentialWeightLocal` | Comparison of weights on balls of radius proportional to h, constant independent of h; input to the proved elliptic estimate |
| `AtomicGroundFineResponse`, `AtomicGroundFineDecomposition`, `AtomicEnergyShiftForcing` | Same correction with sharp bound cΓh⁻³exp(−J/h−β₁log²(1/h)) and energy shift with a single forcing factor |
| `GroundStateCertificate`, `SchurGroundCertificate`, `AtomicGroundTransfer` | Schur-constructed certificate implies variational ground state, one-dimensional eigenspace, gap, and normalized smooth state unique up to phase |
| `ClassicalRadialLowLevels` | A004: positive normalized radial ground state and O(h^(3/2)) bounds for the first two semiclassical levels |
| `RadialOscillatorLevels`, `RadialHarmonicLimits`, `OperatorSecondMinmax`, `SemiclassicalOperator`, `RadialHarmonicAssembly` | Oscillator-level ordering, limits, scaling and min-max complement bound; proved assembly of the radial spectral certificate |
| `RadialCoreSpectralData`, `RadialCoreSpectralAssembly`, `AtomicGroundConstruction` | Radial contract assembled from A004 and realization A002; construction of the actual potential's simple ground state with gap |
| `CoreQuadraticBound`, `RadialCoreVariationalBound`, `MagneticFieldScaling`, `RadialGroundCertificate` | Quadratic core bound, independent variational energy estimate, exact field conversion, and operator-to-test gap transfer, all proved |
| `AtomicGroundEnergyBounds`, `AtomicSourceRegime` | Energy bounds, scaledAtomicEnergy→1 and eventually [1/2,1]; canonical ground state, representation for all L, cell integrability, and hopping identity/reality for R<2L, under explicit analytic interfaces |
| `Main` | Physical assembly and quantifier order |
| `OperatorBridge`, `OperatorMain` | Self-adjoint operator on L², transfer of conclusions, and operator statement |
| `BridgeActionMinimum`, `BridgeActionEnergy`, `LandauKernel`, `LandauKernelDecay` | Exact real minimum, energy derivative, convergence, and exponential rate of the integral kernel |
| `SeparationCertificate`, `ConstructionCuspBounds`, `GeometryActionSlopes` | Uniform separation choice, support geometry, and action slopes |
| `HoppingChannels`, `ParityTransfer`, `SchurBlock` | Cell assembly, transfer, and Schur elimination under their precise hypotheses |
| `HoppingIntegrability`, `HoppingSourceIdentity` | Absolute convergence of the concrete cells; hopping identity from the free resolvent equation |
| `InactiveSupportGaps`, `LandauKernelUniform` | Seven margins on the full supports, uniform exponential kernel rate |
| `InactiveKernelBounds`, `LogFlatIntegral` | Uniform kernel bounds on cells, L¹×L¹ pairing bound, real log-flat integral with arbitrary loss |
| `LandauLaplace`, `LandauLaplaceTails`, `LandauLaplaceLeading`, `LandauLaplaceUniformLeading` | Laplace Hessian, tails, and leading coefficient controlled uniformly in `(E,r)` on positive compact sets at fixed field; relative form and moving parameters, without a differentiated expansion |
| `CoreSourceBound` | Uniform L¹ bound `C h⁻²` for the core source with normalized atomic state |
| `CoreCellBound` | Absolute exponential bound on the actual core–core cell, uniform in the normalized state |
| `LogFlatIntegralLower` | Lower bound for the log-flat integral and uniform logarithmic rate; natural power |
| `CuspChartJacobian` | Injective real chart, change of variables with Jacobian `t²`, and exact reduction of a weighted cusp-potential integral |
| `ComplexCuspGeometry` | Complexified polynomial charts, radii agreeing with real geometry, common analytic bidisk, and normal derivatives `1/2` |
| `ComplexCuspRemainder` | Explicit quadratic remainders of the three complex radii, uniform in tangential variables; division by h negligible on the active window |
| `ComplexLambertRoot`, `ComplexLambertAsymptotics`, `ComplexLambertRegularity` | Constructed complex branch, uniform asymptotic, holomorphy, and derivative on the explicit domain |
| `ComplexLogFlatPhase`, `ComplexLogFlatSaddle`, `ComplexSaddleBranches` | Effective critical point for coefficient c*tStar/h, values, Hessian, size, and angle control |
| `ExponentialRemainderBounds`, `ComplexSaddleLeading`, `ComplexLogFlatLeading` | Horizontal integral: integrable bound after dilation, nonzero complex Gaussian leading term |
| `ComplexLogFlatChange`, `ComplexLogFlatContour`, `ComplexLogFlatErrors`, `ComplexLogFlatNormalization` | Logarithmic substitution, exact ray deformation, exponential errors, and absorption by saddle normalization |
| `ComplexLogFlatAsymptotic` | Nonzero complex leading term for the actual normal integral on (0,t₂), at fixed parameters and natural power |
| `ComplexLogFlatCutoff`, `ComplexLogFlatCutoffAsymptotic` | Exponential cutoff error and complex asymptotic with the potential's actual cutoff p.χa, particularly m=2 |
| `ComplexLogFlatPhaseGrowth` | Continuous sublinear leading-term phase at large coupling; decomposition into positive magnitude and phase |
| `ComplexSaddleAbsolute`, `ComplexSaddleProduct` | Absolute bound after normalization on saddle contours, including their restricted product; control of uniform multiplicative perturbations |
| `LogFlatStretchedErrors`, `LogFlatActiveWindow`, `LogFlatActiveTruncation` | Normal window `T_h=tStar h^(3/4)` containing the saddle, scale `T_h²/h→0`, and truncated-integral asymptotic after actual contour displacement |
| `LogFlatActiveRealTail`, `LogFlatPolynomialErrors` | Uniformly small exterior real tail; absorption of `h^(-N)` factors, even with both complex normalizers |
| `CuspActiveWindow` | Normal window contained in the common analytic domain; actual cutoff p.χa equals 1 there |
| `ComplexLandauKernel` | Actual integral at complex radius, agreement on real radii, convergence, and domination by the real kernel at radius `sqrt(Re(r²))` |
| `ComplexLandauHolomorphic`, `ComplexCuspKernelHolomorphic` | Holomorphy of the actual kernel, joint compositions, and product of the three kernels on a common geometric bidisk |
| `ComplexCuspKernelProfile`, `ComplexCuspPhase` | Relative profiles at the three chart radii, moving energy; exact magnetic phase and exponential correction tending to one on the active window |
| `ComplexCuspPhysicalBridge` | Exact agreement of charts, radii, and phase with the model's Euclidean plane; actual `sourceKernel` connected, sign `exp(+iΦ/h)` verified |
| `BridgeActionTaylor`, `BridgeTimeRadial`, `ComplexLandauEffectiveRadius`, `ComplexLandauAction` | Quadratic radial remainders and critical-time variation; uniform action comparison at the effective radius |
| `ComplexLandauTails`, `ComplexLandauLocalProfile`, `ComplexLandauDecomposition` | Exponentially small complex tails, actual dominated Gaussian profile, and exact integral decomposition |
| `ComplexLandauWindow`, `ComplexLandauAsymptotic` | Complex relative asymptotic `1+o(1)` uniform for `δ=O(h^(3/4))`, moving real energy and radius; no differentiated expansion |
| `UniversalComponentSourceL1`, `OppositeSupportReconstruction`, `AtomicOppositeSupportFineBounds` | Universal L¹ sources, almost-everywhere reconstruction, and sharp masses on the opposite support for the same c and Γ |
| `PhysicalResidualMass`, `CanonicalParityCorrectionMass`, `OppositeSupportEnvelopeComparison`, `CanonicalParityRelativeErrors` | Exact physical residuals, action margin, and defect/two corrections o(envelope) for the channel witnesses |
| `ConstructedMainAssembly`, `ConstructedMainProof` | Final operator conclusion, all original estimates constructed, explicit analytic interfaces |
| `Remaining` | mainConclusion, elementaryPotential_main, and thm_main proved without direct sorry; classical admissions A002–A004 explicitly instantiated |
| `CoordinateRectangleFTC`, `UnitMeasureL2Bound`, `CoordinatePointEvaluation` | Point evaluation by the H² norm, proved using a cutoff, two applications of the fundamental theorem, and Cauchy–Schwarz |
| `ClassicalEllipticSobolev` | Proved wrapper for point evaluation at zero by the H² norm on the unit ball |
| `EllipticCaccioppoli`, `LaplacianHessianEnergy`, `LocalPoissonH2`, `EllipticLocalH2` | Proved cutoff energy bound, Hessian identity, and uniform local H² estimate |
| `CoordinateSobolevProduct`, `EllipticSourceSobolev`, `EllipticSobolevBootstrap`, `EllipticUniformInterior` | Proved higher-order interior estimate, uniform in bounded coefficient jets |
| `CoordinateSobolevEmbedding` | Proved higher-order point bounds from the H² point estimate |
| `EllipticCoordinateNorms`, `EllipticSobolevAssembly`, `ClassicalEllipticInterior` | Proved coordinate/directional norm conversions and assembly of the fixed-ball estimate |
| `StandardLandauResolvent`, `ClassicalLandauResolvent` | A003: the standard integral kernel for the closed free Landau operator at Planck constant one |
| `MagneticInhomogeneousDomain`, `LandauResolventScaling` | Proved passage from smooth L² solutions to the closed domain and exact field, energy, kernel, and source-integral scaling |
| `LandauIntegrandODE`, `LandauRadialDerivatives`, `LandauProperTimeEndpoints`, `LandauProperTimeIntegral`, `LandauRadialEquation` | Two differentiations under the integral, limits at both endpoints, and exact radial ODE of the integral kernel, without further identification with a singular Green function |
| `LandauRadialL2`, `RadialWronskian`, `RadialCaccioppoli`, `RadialExteriorCutoffs`, `RadialExteriorEnergy`, `LandauExteriorUniqueness` | Exterior L² kernel branch and real uniqueness from the ODE and L² alone; derivative energy deduced, positive proportionality ΓK for a positive solution |
| `RealRadialState`, `MagneticRadialReduction`, `RadialPlaneL2`, `RadialCoreExteriorState` | Calculation of the actual radial Hamiltonian, polar passage from L², and exact exterior formula for the actual normalized positive ground state; wrapper through A002+A004, no bound on Γ admitted |
| `RadialEigenfunctionEquation`, `CoreRadialMonotonicity`, `RadialGroundMonotonicity`, `RadialProfileLower`, `RadialCenterLower`, `RadialCoreProfileEstimates` | Full ODE and decreasing actual core profile; uniform positive bound on [0,h] from mass and flux |
| `RadialWronskianComparison`, `RadialCoreKernelComparison`, `RadialCoreNormalizationLower` | Comparison with the same ΓK for all r>0; Γ≥c h² and Γ⁻¹≤C h⁻² assembled and proved without A003 or pointwise harmonic convergence |
| `LandauExteriorConvolution`, `RadialCoreSourceRepresentation`, `RadialLandauAverage`, `RadialCoreNormalization` | Exterior continuity and pointwise representation of the actual source; polar change of variables and exact integral formula for the same Γ, with an explicit free-kernel interface, supplied by A002+A003 |

## Contribution guidelines

1. Never replace an estimate relative to the positive envelope with one
   relative to the absolute value of hopping, which can vanish.
2. Fix the potential, all its parameters, and `L₀` before choosing `L ≥ L₀`.
   Coupling thresholds may subsequently depend on `L`.
3. Do not identify the sequence of hopping zeros with the sequence of crossings.
4. A proved structure contract must include a proof that an instance exists.
5. Update the code, English admission documentation, and graph together.
6. Admit only classical or readily verifiable facts, with a precise reference
   and a natural-language proof. Prove the original estimates for the concrete
   potential; do not replace them with an axiom.

The historical [preparatory note](<note_formalisation (1).pdf>) is also available in English,
with editable [LaTeX source](docs/PREPARATION_NOTE.tex). It records the initial plan,
not the current proof status. To rebuild it from the repository root:

```sh
mkdir -p /tmp/infinite-zero-preparation
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/infinite-zero-preparation docs/PREPARATION_NOTE.tex
cp /tmp/infinite-zero-preparation/PREPARATION_NOTE.pdf 'note_formalisation (1).pdf'
```
