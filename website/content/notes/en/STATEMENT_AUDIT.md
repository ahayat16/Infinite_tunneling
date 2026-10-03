# Audit of the main statement

This guide compares the manuscript's
[`thm:main`](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L222)
with its Lean statement, definitions, and proof dependencies.

**`thm_main` is proved with no `sorry` of its own, modulo the four
classical admissions A002–A005.** It retains exactly the type
`ConstructedPotentialMainTheorem`, with no `FixedAnalyticData` argument
or hypothesis asserting the existence of suitable data. The proof in
[Remaining.lean](../InfiniteZero/Remaining.lean) proceeds through the
stronger result `elementaryPotential_main`, which literally fixes the
elementary parameters. Transitive classical dependencies remain explicit;
no original tunneling estimate is admitted.

## Potential and quantifiers

The target definition is in
[`OperatorMain.lean`](../InfiniteZero/OperatorMain.lean#L209):

```lean
∃ p : CuspParameters, p.BasicConditions ∧ AdmissiblePotential p.potential ∧
  ∃ L₀ : ℝ, p.R < L₀ ∧
    ∀ L, L₀ ≤ L → OperatorMainConclusion p.b p.potential L
```

Here `p` simultaneously fixes all scalars and both cutoff functions before
`L₀`, and therefore before **every** `L ≥ L₀` and every coupling.
It contains neither `L` nor `λ`. `BasicConditions` implies `p.b > 0` and
`p.R > 0`, so `p.R < L₀` implies `L₀ > 0`. The sequences and thresholds
inside `OperatorMainConclusion` are chosen after `L` and may depend on it.
The theorem `ConstructedPotentialMainTheorem.toOperatorMainTheorem` proves
the passage to the manuscript's existential order
`∃ b, L₀, v, ∀ L ≥ L₀`.

The formula is not an arbitrary abstract potential:
[`Construction.lean`](../InfiniteZero/Construction.lean#L73) imposes

\[
v_p=v_p^\circ+\varepsilon_p(q_{+,p}+q_{-,p}),\qquad
v_p^\circ(x)=
\begin{cases}
-e^{-|x|^2/(r_0^2-|x|^2)},&|x|<r_0,\\
0,&|x|\ge r_0,
\end{cases}
\]

with `q₊ = −a exp(−β log²(t*/t)) χa(t) χb(s)` in the cusp
`0<t<t₀`, `|s|<s₀`, extended by zero, and `q₋(x₀,x₁)=q₊(x₀,−x₁)`.
The frame and tip `(R/2, √3 R/2)` are also fixed by the formulas in the
code. This matches the manuscript's explicit core and construction with
two cusps, and strengthens its purely existential statement about `v`.

The proof chooses **`elementaryParameters`**: `r₀=1`, `R=16`, `b=1`,
`ε=1/16`, `a=β=tStar=s₀=1`, `t₀=1/100`, with explicit smooth cutoffs.
The separation certificate is constructed after this choice.
The theorem `elementaryPotential_main` establishes the conclusion for
this same potential and every `L≥L₀`. `thm_main` is its existential
corollary: no additional compatibility of parameters remains to be assumed.

## Correspondence of the conclusions

This table describes the conclusions established, modulo A002–A005.

| Manuscript requirement | Lean formulation and audit result |
|---|---|
| The same nonradial `v∈C_c∞(ℝ²;[-1,0])` for every `L≥L₀` | `AdmissiblePotential p.potential`, chosen before `∀ L`. Its properties already follow from `BasicConditions` through `CuspParameters.admissiblePotential`. |
| (i) Infinitely many crossings, `λₙ→∞` | `MainConclusion.spectral_zeros` requires a positive, strictly increasing, divergent sequence with `secondEnergy−groundEnergy=0`. These are variational values: see the translation limit below. |
| An exactly double ground level, even and odd, at every sufficiently large crossing | `large_crossings`, then `OperatorMainConclusion.large_operator_crossings`, cover **every** zero of the min-max gap beyond a threshold. `OperatorDoubleGround` requires complex dimension two and two nonzero eigenvectors of opposite parity. |
| The actual two lowest levels | `realization.lower_bound` gives the global bottom of the form on the domain; `eventual_ground_gap` imposes a positive gap on the orthogonal complement. `arbitrarily_large_operator_crossings` yields isolated two-dimensional L² ground eigenspaces at arbitrarily large couplings. |
| (ii) Infinitely many zeros of `ρλ` | `MainConclusion.hopping_zeros` requires a second positive, strictly increasing, divergent sequence and the **complex** equality `canonicalHopping=0`. It is not identified with the crossing sequence. |
| (iii) Infinitely many parity changes | `operator_parity_changes` requires `0<pₙ<qₙ<pₙ₊₁`, with both sequences divergent, a simple even ground state at `pₙ`, and a simple odd ground state at `qₙ`. |

The fields are defined in
[`MainConclusion`](../InfiniteZero/Main.lean#L164) and
[`OperatorMainConclusion`](../InfiniteZero/OperatorMain.lean#L101).
The operator is the closure of the concrete test graph on
`Lp ℂ 2 volume`, through [`magneticOperator`](../InfiniteZero/OperatorBridge.lean#L76).
The Hamiltonian `ΣDⱼ²+λ²V`, its gauge translations, and the hopping in
[`MagneticModel.lean`](../InfiniteZero/MagneticModel.lean#L99) have the same
signs and factors as the TeX equations, with
`V(x)=v(x+d)+v(−x+d)`, `φᴿ(x)=φᴸ(−x)`, and the factor `λ²=h⁻²`.
Covariance and mass preservation are proved; the same atomic state is
used on both sides. Finally, `atomic_states` and `hopping_intrinsic`
ensure that this is an existing normalized state and that the coefficient
is independent of its phase choice.

## Exact limits

The code does not construct the enumeration `E₀≤E₁≤…` of the discrete
spectrum used in the TeX. `groundEnergy` and `secondEnergy` are defined
by an infimum and a min-max over test functions. For the constructed
potential at large coupling, `ConstructedGlobalMinmax` proves that
these two values are exactly the minimum and maximum of the actual sector
eigenenergies. The global spans and their normalized physical representatives
are established by `ParityGroundEigenspaces` and `PhysicalParityModes`,
with an actual gap above the ground eigenspace, including at crossings.
The even/odd bottoms remain defined variationally, rather than literally
by `inf σ`. Enumeration of the entire spectrum, a full spectral window,
and its rank-two projection are not claimed; see
[GLOBAL_PARITY_DOUBLET.md](GLOBAL_PARITY_DOUBLET.md).

The target adds realization interfaces and an explicit gap to express
its physical content. A002, A003, A004, and A005 are the registered
classical admissions: operator realization, the Landau resolvent,
harmonic approximation for the radial core alone, and an elliptic
estimate on a fixed ball. None constructs tunneling data.
The simple ground state and gap for the full potential are deduced in
Lean from A002+A004; source representations also use A003.
Exterior Agmon decay of the actual canonical ground state is likewise
deduced from A002+A004 in
`CuspParameters.canonicalAtomicState_agmon_tail`: constants and the
threshold are chosen before the coupling, and no energy or existence
hypothesis for this state remains for the caller to supply.
This absolute exponential bound is a separate step from the relative
estimates subsequently established for tunneling.
The wrappers `atomicGroundEnergy_exponential_comparison` and
`atomicGroundVectors_exponential_comparison` also establish an exponential
comparison with the radial core, from `BasicConditions` alone modulo
A002+A004. The former compares the actual unscaled ground energies;
the latter constructs normalized ground eigenvectors of both operators,
close in `L²`, with a positive real inner product.
The phase choice is relative and asserts neither continuity of the
canonical choice in the coupling nor a pointwise or weighted source estimate.
The [details of the proof](ATOMIC_COMPARISON.md) preserve this distinction.
`AtomicCuspWeightedInverse` then constructs the compressed inverse with
the exact Lipschitz cusp weight, from the radial data and explicit
realizations. Its norm is at most `12/(γλ)` for `E≤Ecore`, hence at the
full atomic energy; constants precede `λ`, the reference precedes `E,κ`,
and the resolvent precedes `κ`. This result admits no estimate specific
to the cusps and does not use A003. It claims neither the `E>Ecore`
part of the manuscript's window nor pointwise source estimates;
the [proof and its scope](CUSP_WEIGHTED_INVERSE.md) detail this variant.
The [exterior radial block](RADIAL_EXTERIOR_KERNEL.md) proves the
ODE of the integral kernel and uniqueness of its real L² branch,
with derivative energy deduced. `RadialCoreExteriorState` applies
this result to the actual core ground state and concludes `φcore=ΓK`,
`Γ>0`, for `r>r₀`.
A004 was extended to include the classical positive radial choice, with
a reference and natural-language proof; the differential reduction and
passage to the measure `r dr` are proved separately in Lean.
The canonical choice is not declared positive.
The decreasing real profile, a bound `f(r)≥c>0` on `[0,h]`, and
the comparison `f≤ΓK` are proved. The compiled assembly
`RadialCoreNormalizationLower` gives `Γ≥c h²` and `Γ⁻¹≤C h⁻²`,
under A002+A004 alone. Constants are fixed before the coupling,
and the bounds concern the coefficient of the same state and its same tail.
This is a weaker variant than `h^(3/2)` in Appendix B, sufficient for
the polynomial losses of L7.1 and L8.2 under their strict exponential
reserves. Neither literal B.1 nor the differentiated expansion is claimed.
The auxiliary convolution identities use A003 separately;
see [the details](RADIAL_NORMALIZATION.md).

The positive radial choice carries the same test-function gap,
by simplicity of the core and invariance under unitary phase
(`RadialCoreGroundChoice`). It is retained in the weighted inverse
and then in the Schur certificate for the actual full ground state.
The wrapper `CuspParameters.atomicGround_weighted_decomposition`
requires only `BasicConditions`, modulo A002+A004: it constructs the
weight, actual normalized smooth ground states `φcore,ψfull`,
and `c∈[1/2,1]` such that `η=ψfull−cφcore` is orthogonal to `φcore`,
has weighted mass at most `C² exp(−2dλ)`, and satisfies the exact
pointwise differential equation.
The states and `c` are chosen before the weight strength `κ`.
The bound in terms of the actual forcing
`‖Mκ η‖₂≤12cλ/γ·‖Mκ Wφcore‖₂` is also proved.
The connection to [refined forcing](CUSP_FINE_FORCING.md) then preserves
the exact action rate and log-flat factor in the weighted norm of this
same correction. The wrapper `atomicGround_fine_response_data` now
assembles the [complete data for its PDE](ATOMIC_FINE_RESPONSE_DATA.md):
the weighted derivatives of both terms are controlled in local L²
at every fixed order, with a single factor `cΓ`, still through
A002+A004 only. The exact PDE and local data are then used in the
[elliptic connection](ATOMIC_RESPONSE_JETS.md):
`atomicGround_fine_response_jets` yields pointwise estimates for all
jets through a fixed order, via A002+A004+A005.
The hypotheses of the classical estimate A005 are verified for the
actual operator. The [scattered-source profile](CUSP_SCATTERED_SOURCE.md)
is assembled for the same states and coefficient Γ:
`λ²Wη` simultaneously preserves the local and global log-flat factors,
with polynomial loss λ⁶, on the closed supports and at the tips.
This connection requires no new admission.
`atomicGround_source_profiles` also assembles an upper bound for the
incoming source, with exact action and polynomial prefactor `λ^(n+4)`,
for the same choice of `φcore,ψfull,c,Γ` on both cusps.
The three log-flat margins are independent, and constants precede λ.
This [simultaneous bound](CUSP_SOURCE_PROFILES.md) is a source upper
bound; the relative incoming formula is obtained separately through
the saddle modules and channel assembly described below.
The [L¹ norms](CUSP_SOURCE_L1.md) are then deduced through the actual
change of variables, with Jacobian t² and factor 2s₀.
The full components of this same state satisfy the cusp bound
`CΓλ⁶exp(−λJ−β₁log²λ)`, for every `0<β₁<β`, and the core bound
`Ccoreλ²`. The global log-flat cost of the scattered part adds to the
local integration gain; it is not spent to obtain the latter.

The connection to the [seven inactive cells](INACTIVE_CELLS.md) is
proved in `atomicGround_inactive_cells`: each is bounded by
`C(Γ²+1)λ¹⁰exp(−λ(Aref+31δhop))`, with the same states and Γ.
Constants precede λ. Simplicity of the ground state and exact invariance
under unitary phase transfer these bounds to the canonical cells.
The full energy remains in the bridge kernel, and the core energy
in the radial tails.
The quotient `(Γ²+1)/(c²Γ²)` is controlled by `4Dλ⁴` for this same
coefficient; the inverse square of the scalar saddle size is absorbed
by any strict exponential reserve, even with polynomial losses.
Their assembly `atomicGround_inactive_relative_tex` gives all
seven bounds and the sum of their norms, actual and canonical, by
`C * activeSaddleTexEnvelope * exp(−15δhop λ)`.
The comparison of Gaussian factors using `Re w` and `1+w` is also
proved; the connection preserves the same coefficients and does not
assume the active conclusion.
The canonical connection `canonical_inactive_relative_tex` is universal
in the supplied positive radial state, its exterior coefficient,
and every `c≥1/2`. It uses uniqueness of the positive ground state
and of Γ, then `c₀²≤4c²`; it imposes no identity between c and an
unexported overlap.
The [exact incoming formula](INCOMING_SOURCE_FORMULA.md) already connects
the physical integrand to the three complex kernels; the exact integral
change of variables is proved with the Jacobians and outside factor.
The [active reduction](ACTIVE_SCATTERED.md) controls the difference
between the full and incoming cells, also for the canonical cell, by
`C enveloppeTex exp(−(β/8)log²λ)`, with the same φψcΓ.
The bridge kernel preserves the exact action, the L¹ norms supply the
costs 3β₀/4β₀, and the inverse square of the saddle consumes only 2β,
up to an arbitrarily small margin.
The [normalization of the incoming density](INCOMING_MULTIPLIER.md)
is exact, with the two energies kept distinct.
The bounds `Ecore=1+O(h)` and `Efull=1+O(h)` justify freezing the slope
at its limit without replacing the action or moving coefficients.
The normalized physical profile tends uniformly to 1 on the complex
window `tStar h^(3/4)`. Its holomorphy and integrability on the saddle
contour are proved; the normalized integrated error tends to zero there,
uniformly in the tangential variables.
The [return to the physical density](INCOMING_PHYSICAL_ASYMPTOTIC.md)
is assembled: real truncation, two deformations with integrable
hybrids, exact changes of variables, and the factor tStar⁶.
Tangential integration gives the limit
`N_h² Z_h incomingCuspIntegral → tStar⁶(π/β)Bs²`.
The [connection to source forcing and channels](ACTIVE_CHANNEL_ASYMPTOTIC.md)
is proved. `IncomingCellTexAsymptotic` preserves the negative sign,
the factor λ⁶√λ, and the two saddle phases.
`ConcreteChannelWitnesses` chooses the states and cΓ once for all
estimates. `CanonicalChannelAsymptotics` actually constructs the channels
and the hopping cosine formula, with their explicit amplitude and phase.

The `*_of_analytic_data` helpers are conditional assemblies and do not
replace `thm_main`. The self-adjoint parity restrictions, abstract
mode constructor, and identification of their energy with `parityEnergy`
are proved; `DoubleWellParityGround` assembles them for the concrete
potential, with a threshold before λ and L and a common absolute lower
bound on the complements of the actual modes.
The first two global min-max levels are identified, via A002+A004,
by `doubleWell_global_minmax hp cert`.
The `TwoModeRealization` package and global gap are assembled;
`doubleWell_twoModeRealization hp cert` directly supplies the modes
required by `LocalChannelAnalyticData.modes`.
Its corollary `doubleWell_spectral_realization hp cert` gives the
`SpectralRealization` contract via A002+A004, with a threshold before L.
`CanonicalParityRelativeErrors` proves that the actual defect
and both Schur corrections are `o(A)` for the same channel witnesses.
`ConstructedMainProof` assembles these results without any additional admission.
`CuspParameters.exists_canonicalHopping_continuous_of_radialData`,
in `HoppingContinuity`, proves continuity of the canonical complex hopping
on a half-line whose threshold precedes every separation `L`, under
radial data and explicit realizations, with no admission in this result.
The compiled wrapper `CuspParameters.canonicalHopping_continuous hp`
instantiates A002+A004; no continuous canonical phase is assumed.
Continuity of the parity energies and `signedSplitting` on all λ>0
is proved for the constructed potential.
No spacing, uniqueness of zeros, or identity between their two sets
is claimed.

The final connection uses the same coefficients `W.c` and `W.Γ`
as the hopping envelope. The universal L¹ norms and reconstruction
of the actual state on the opposite support give a mass
`≤C c²Γ² λ¹² exp(−2λ(G+J))`, with `G=J(Ecore,R)` and
`J=J(Efull,2L−R)`. The exact operator residuals give the powers
`λ¹⁴` for the defect and `λ¹⁵` for the Schur corrections.
The action reserve `J` makes them negligible relative to the active
envelope with action `2G+J`, including its saddle cost.
No incompatible choice of state is involved: the positive core reference
is unique, and the source norms of the full ground state are invariant
under unitary phase.

`ConstructedMainAssembly` combines modes, gap, and continuity statements
using a common threshold. `ConstructedMainProof` supplies the actually
constructed asymptotic and Schur package.
`CuspParameters.mainConclusion` instantiates the four classical interfaces,
then `elementaryPotential_main` and `thm_main` give the final conclusions.

The proof targets the three items of the boxed theorem.
It claims neither a differentiated remainder rate, monotonicity of the
phase, nor zero spacing or uniqueness.
The continuous asymptotically linear phase and `o(1)` error suffice
for the sign and intermediate-value arguments.
