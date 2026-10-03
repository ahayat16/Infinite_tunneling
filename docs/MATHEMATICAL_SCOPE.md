# Statement scope and fidelity to the manuscript

## Target

The reference is `thm:main`, lines 222–241 of [`Infinite_Zero_Tunneling_Lean_oriented_V2.tex`](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex). The target requires `∃ b>0, ∃ L₀>0, ∃ v`, then `∀ L ≥ L₀`: the potential must be independent of both separation **and** coupling. Sequences and asymptotic thresholds may depend on the fixed separation.

The strengthened target `ConstructedPotentialMainTheorem`, used by `thm_main`, requires the core-and-two-cusp formula `p.potential`:

```lean
∃ p : CuspParameters, p.BasicConditions ∧ AdmissiblePotential p.potential ∧
  ∃ L₀ : ℝ, p.R < L₀ ∧
    ∀ L, L₀ ≤ L → OperatorMainConclusion p.b p.potential L
```

Parameters must be **chosen in the proof**, rather than assumed capable of producing tunneling. No spectral or asymptotic hypothesis appears in this statement. `p.BasicConditions` and admissibility are existential conclusions to establish, not premises. Passage to the manuscript's existential statement is proved by `ConstructedPotentialMainTheorem.toOperatorMainTheorem`. Details are in the [statement audit](STATEMENT_AUDIT.md). The proof now chooses `elementaryParameters`. The stronger result `elementaryPotential_main` fixes this potential literally, then constructs L₀ before every admissible separation. `thm_main` deduces the existential target without a `sorry` in its body, but with the four classical admissions A002–A005 in its transitive dependencies.

The three retained conclusions are exact crossings of the first two levels, with multiplicity two and modes of opposite parity; hopping zeros; and infinite alternation of simple ground-state parity. Asymptotic spacing π/Φ*, announced in the introduction but absent from `thm:main`, is not included in this initial goal.

## Actual physical definitions

`Plane = EuclideanSpace ℝ (Fin 2)` carries Lebesgue measure. The potential is real-valued; wavefunctions are complex-valued. The code directly defines

\[
D_j=-i\partial_j-\frac{b\lambda}{2}(x^\perp)_j,
\quad H=\sum_jD_jD_j+\lambda^2 V,
\quad V(x)=v(x+d)+v(-x+d).
\]

Derivatives are real Fréchet derivatives in coordinate directions. Classical eigenfunctions are **all** smooth L² functions satisfying the equation pointwise, rather than an arbitrarily chosen abstract subspace. Measures and integrals are those of Mathlib.

`groundEnergy`, `evenEnergy`, and `oddEnergy` are infima of the magnetic form over the appropriate normalized test functions. `secondEnergy` is the second min–max value over two-dimensional complex subspaces of test functions. These definitions alone do not prove nonemptiness, bounds, or the dense-core property.

Hopping is the **complex** integral

\[
\lambda^2\int\overline{\phi^L(x)}v(x+d)\phi^R(x)\,dx,
\quad \phi^L=T_{-d}\phi,\quad\phi^R(x)=\phi^L(-x),
\]

with `T_a φ(x)=exp(-i bλ(x∧a)/2) φ(x-a)`. The same atomic state is used on both sides. Its canonical choice depends only on b, v, and coupling. Its simplicity at large coupling is deduced in Lean from A002+A004; invariance of the coefficient under unit-phase changes is proved. In the main theorem, zeros are indeed complex equalities to zero: reality of hopping follows from the source representation and cell conjugation. Universal identification of the kernel with the resolvent is classical admission A003. `MagneticCovariance` proves DⱼTₐ=TₐDⱼ, Hamiltonian covariance, inversion, and preservation of L² and mass. `LandauResolventBridge` rigorously deduces the right-state representation under this universal contract, with a smooth compactly supported source and the correct h² factor.

## Justified departures

1. **More general final real analysis.** Continuity of the phase on a half-line and its divergence suffice to reach the cosine levels. Monotonicity is unnecessary. In the physical application, divergence follows from Θ(λ)/λ→Φ* and the verified calculation Φ*>0. The Lean result is more general at this point and its proof is complete.
2. **Remainder expressed as a limit.** The code requires only e→0 and a transfer error o(A). The text's O(1/log λ) and exponential bounds imply these hypotheses. The sufficient variants e→0 and o(A) are now proved for the fixed potential. The literal O(1/log λ) rate and remainder differentiability are not claimed.
3. **Variational energies and unbounded operator.** The `Main.lean` core uses the classical min–max/PDE formulation. `OperatorBridge.lean` additionally defines the canonical Mathlib unbounded operator (`LinearPMap`) on `Lp ℂ 2 volume` by closure of the test graph. Classical interface A002 asserts self-adjointness and correspondence with the variational model and classical eigenspaces. Dimension and parity transfers are proved and used in `OperatorMain`. The target `thm_main` thus genuinely concerns this operator. The auxiliary `thm_main_from_analytic_data` takes analytic data as arguments and uses classical admissions A002 and A003. The core `constructed_main_of_analytic_data` receives their contracts explicitly and itself depends on no `sorry`. A quadratic lower bound on the whole domain, combined with a two-dimensional eigenspace at that level and a **positive gap on its orthogonal complement**, expresses degeneracy of the first two discrete levels without enumerating the whole spectrum. The predicate `HasGapAboveGround` is proved in the spectral assembly; it does not follow automatically from finite dimension and is not part of A002.
4. **Local geometry in pairs of reals.** `Geometry.lean` uses `ℝ × ℝ` with length defined as the square root of the sum of squares, rather than Mathlib's product norm. The physical model uses the Euclidean plane. `Construction.phase_pos` relates the proved scalar coefficient to the parameters actually used.
5. **Wider normal window.** `LogFlatActiveTruncation` proves the same saddle limit for truncation T_h=tStar h^(3/4). This contains the saddle of order h log(1/h); T_h²/h→0 and contour errors are O(exp(−d h^(−1/4))), still negligible after normalization. This choice targets the relative o(1) error sufficient for oscillation and avoids an optimal window. The actual phase and amplitude bounds and their application to the active cell are now proved in the corresponding physical modules.

## Scope of the new proved analytic calculations

For each **fixed** b,E,r>0, `LandauLaplaceLeading` proves

\[
h^{3/2}e^{J_{b,E}(r)/h}K_{b,h,E}(r)
\longrightarrow
\frac{b}{4\pi\sinh(b\tau_*)}
\sqrt{\frac{2\pi}{F''(\tau_*)}}>0,
\qquad \tau_*=\operatorname{bridgeTime}(b,E,r).
\]

This is the actual leading coefficient of the proper-time integral, without admissions. `LandauLaplaceUniformLeading` now strengthens this limit to uniform convergence on every positive real compact set in (E,r), including relative convergence, and handles moving parameters. This is not a differentiated expansion. The uniform logarithmic rate and tail estimates are separate results. Identification with the resolvent operator remains A003.

`ComplexLandauAsymptotic` also proves a uniform relative **complex** asymptotic at r+δ, |δ|≤M tStar h^(3/4), with linearized action J(E,r)+J′(E,r)δ and coefficient k₀(E,r). The real energy and radius may vary in positive compact sets. This order-zero version suffices for the intended active-window assembly; it claims neither complex energy nor a differentiated expansion on fixed complex neighborhoods. The proof keeps proper time real, uses local Gaussian domination, and transfers tails to radius sqrt(Re((r+δ)²)); see [details](SHRINKING_COMPLEX_KERNEL_PLAN.md). `ComplexLandauHolomorphic` now proves holomorphy of this integral on Re(r²)>0: local domination by a fixed real kernel and Cauchy's estimate allow differentiation under the integral. `ComplexCuspKernelHolomorphic` deduces joint holomorphy of the three actual kernels and their product on a geometrically fixed bidisc. The connection to exact incoming sources and their physical integral is proved separately in `AtomicCuspKernelProfile` and `AtomicIncomingIntegralAsymptotic`.

`ComplexCuspKernelProfile` applies the asymptotic to chart radii, with linear normalizations t/2 and (t+u)/2. Energy varies, tangential variables are merely bounded, and normals are O(tStar h^(3/4)). `ComplexCuspPhase` proves the polynomial magnetic-phase formula and that its remainder divided by h tends to zero on this window. These kernel and geometry proofs do not replace eigenfunction estimates in the sources. `ComplexCuspPhysicalBridge` exactly identifies these charts with p.cuspChart and its reflection on the Euclidean plane. It proves agreement of norms and the actual `sourceKernel`, including the sign exp(+iΦ/h); these equalities require no spectral hypothesis.

`CuspChartJacobian` proves chart injectivity on t>0, its inverse, exact Jacobian t², and the change of variables for Euclidean measure. It actually reduces ∫ |q₊(x)| exp(−a t(x)/h) dx to the normal integral with factor t² and the tangential cutoff integral. The log-flat upper bound thus applies to an integral of the cusp **potential**. Fine bounds on actual sources additionally use eigenfunction controls, now established in the source modules.

`ComplexCuspGeometry` complexifies the polynomial charts actually used. The principal square root of the sum of squares recovers the Euclidean radius at real points. For tangential variables in a compact rectangle, a common normal bidisc lies in the analyticity domain of both source radii and the bridge radius. Their tip values are R,R,2L−R, and the four normal derivatives equal 1/2. These geometric calculations alone do not prove holomorphy of atomic amplitudes. `ComplexCuspRemainder` establishes the three radii's quadratic errors through explicit factorizations, uniformly in tangential variables. Their sum divided by h tends to zero on the active window. Corresponding total-action and amplitude estimates are not assumed as immediate consequences in these declarations.

`ComplexLambertRoot` constructs by contraction a solution of w + Log w = L in a nonempty quantitative domain, and proves uniqueness among solutions with real part at least two. For L=ℓ+d, ℓ→∞, `ComplexLambertAsymptotics` proves uniformly on every set ‖d‖≤M

\[
w=L-\Log L+O(\log\ell/\ell)
  =\ell-\log\ell+d+o(1).
\]

This is not an implicit definition assumed to have a solution. `ComplexLambertRegularity` also proves holomorphy and the derivative on the explicit domain. `ComplexLogFlatSaddle` constructs the critical point for the actual coefficient c*tStar/h and proves its exact identities. The logarithmic substitution, contour deformation, error bounds, and Gaussian convergence are then verified separately.

`CuspParameters.tendsto_normalCutoffIntegral_normalized` finally proves the nonzero complex leading term of ∫₀ᵗ⁰ χa(t)t^m exp(−β log²(t*/t)−ct/h)dt, with **the constructed potential's actual cutoff**, for `m : ℕ` and Re c>0. The Jacobian power m=2 is included. The normalizer is sqrt(Re w) exp(f(yc)) and the limit is tStar^(m+1) sqrt(π/β).

The phase of this leading term is continuous on a half-line in λ=1/h and is o(λ) (`ComplexLogFlatPhaseGrowth`). Absolute control in `ComplexSaddleAbsolute` bounds a uniform multiplicative perturbation on the contour without losing complex cancellation. Contours truncated to the window described above remain in a normal disc of radius T_h; the truncated model integral has the same leading term.

This limit is at fixed parameters, with relative o(1) error; it does not certify the manuscript's rate, all uniformities, or derivatives. Control of the atomic source, four-variable physical multiplier, and scattered contributions is now proved separately, then assembled in `CanonicalChannelAsymptotics`. The scalar model alone does not supply these estimates; see [COMPLEX_SADDLE.md](COMPLEX_SADDLE.md).

The atomic block now has an assembly on the actual operator, in `AtomicGroundConstruction.eventual_atomicGround_properties_of_radialData`. For fixed p satisfying `BasicConditions`, its inputs are classical core and full-potential realizations, and `RadialCoreSpectralData p.b p`: a normalized core ground state, its rescaled energy ≤−1+B/λ, and a gap inequality γλ on tests, uniformly at large couplings. Their existence is now classical admission A004, `radial_core_spectral_data`, justified by magnetic harmonic approximation of the radial core alone; A004 contains no nonradial, source, or tunneling result.

From these inputs, the code constructs the full-potential ground state, proves its simplicity up to phase, isolation, and energy inequality with the core. `exists_atomicGroundCertificate_of_radialData` retains gap bound γλ/2, or γh/2 after rescaling. It assumes no nonradial eigenstate or gap. The wrapper `CuspParameters.eventual_atomicGround_properties` supplies these inputs through A002 and A004: from `BasicConditions` alone, the full-potential ground state exists, is simple and isolated at every sufficiently large coupling, and its energy is at most the core energy. These conclusions therefore rely on the two classical admissions, rather than a Lean proof of their contents.

The intermediate steps are established: pointwise then integrated IMS on tests, with integrability deduced; adapted cutoffs and bounded error; exterior mass O(1/λ) from the closed radial graph (`AtomicExteriorGraph`); complement coercivity on the operator domain (`AtomicSpectralCoercivity`). `MagneticTestGraph`, `WavefunctionL2Bridge`, and `MagneticGraphLowerBound` ensure transfer to L² classes and graph closure. This route assumes no integrability of the noncompact ground state's energy density and claims no general IMS identity on the closed form domain.

`AtomicPerturbationDomain` identifies core and full-potential domains. `OrthogonalCompression` constructs their actual compression and proves self-adjointness; the coercive inverse and its energy continuity give a Schur root and eigenvector. `SchurGroundState` proves this vector is a ground state with a gap; `GroundStateCertificate` identifies the variational infimum and dimension one; `AtomicGroundTransfer` supplies smooth normalized representatives and pointwise simplicity.

`AtomicGroundEnergyBounds` complements this assembly with

\[
 -\lambda^2\le E_{\rm atom}(\lambda)\le-\lambda^2+B\lambda,
 \qquad 1-B/\lambda\le\operatorname{scaledAtomicEnergy}(\lambda)\le1.
\]

The positive resolvent energy therefore tends to one and eventually belongs to [1/2,1]. These conclusions are proved with radial data and realizations as explicit arguments, without `sorry` in the module. `AtomicSourceRegime` assembles them with the free-kernel contract. The wrapper `CuspParameters.atomic_source_regime` in `Remaining` supplies these arguments through A002+A003+A004 and requires only `BasicConditions`.

A common threshold, independent of L, ensures the canonical state is an actual normalized ground state, simple up to phase and isolated; its resolvent representation holds for every L. For R<2L, all nine cells are absolutely integrable. The methods `AtomicSourceFacts.hopping_eq_source` and `AtomicSourceFacts.hopping_real` then identify hopping with the total source pairing and show its imaginary part vanishes. These facts are neither an amplitude estimate nor a proof of coupling continuity.

`MagneticLocalEnergy` establishes the energy identity for the actual eigenfunction multiplied by a smooth real compactly supported cutoff. `MagneticAgmonLocal` and `MagneticAgmonWeighted` give the local inequality with weight exp(F), where F is smooth without a global boundedness assumption. All integrability follows from the support of the cutoff and its derivatives, without assuming form integrability for the noncompact eigenfunction. `AtomicAgmonRegion` eventually deduces a spectral margin λ²/4 outside the core, then the local estimate for cutoffs in that region, even when they meet the cusps.

[`MagneticAgmonBounded`](../InfiniteZero/MagneticAgmonBounded.lean) now removes cutoffs by L² dominated convergence for a bounded smooth weight. `AtomicAgmonWeight` constructs the fixed weight before λ, with squared gradient ≤λ²/16; the remaining margin is λ²/8. [`AtomicAgmonGlobal`](../InfiniteZero/AtomicAgmonGlobal.lean) proves for the core and full potential the bound ∫_{‖x‖≥4r₀}|φ|²≤(C/λ²)exp(−2dλ) under λ>0, E≤−3λ²/4, and mass φ=1. All integrability is deduced; no additional global form domain is assumed. See [AGMON_DECAY.md](AGMON_DECAY.md). `AtomicGroundAgmon` supplies this decay for actual ground states at large coupling. The wrapper `canonicalAtomicState_agmon_tail` retains only `BasicConditions`, modulo A002+A004; the threshold is fixed before λ.

`AtomicPerturbationTail` and `AtomicResidualDecay` turn the radial tail into a bound on the actual residual ‖λ²Wφ₀‖₂≤Kλ exp(−dλ). `AtomicSchurReference` retains the same radial state in the full-potential domain. `SchurGroundQuantitative` then constructs, from a single root, the ground-state certificate and correction ζ, with exact vector φ₀−ζ, ‖ζ‖≤‖B‖/g, and 0≤a−E≤‖B‖²/g.

The assembly `AtomicGroundComparison` proves, at large coupling, 0≤Ecore−Efull≤C exp(−dλ). It also constructs two actual normalized ground vectors u,v∈L² with ‖v−u‖₂≤C exp(−dλ), Re⟨u,v⟩>0, and Im⟨u,v⟩=0. Constants and threshold are fixed before λ for each potential satisfying `BasicConditions`. Both wrappers `atomicGroundEnergy_exponential_comparison` and `atomicGroundVectors_exponential_comparison`, in `Remaining`, use only A002+A004; the conditional modules are admission-free.

The abstract normalization coefficient is c=(1+‖ζ‖²)⁻¹ᐟ², with 0<c≤1 and 1−c≤‖ζ‖². Its insertion into the certified vector and the positive relative phase of actual states are proved. No separate c_h→1 theorem is stated here; coupling continuity, equality of canonical phases, or pointwise state estimates are not claimed by this comparison. See [ATOMIC_COMPARISON.md](ATOMIC_COMPARISON.md).
The weighted inverse is now constructed in `AtomicCuspWeightedInverse` for the exact Lipschitz cusp weight and all energies E≤Ecore, hence at the full ground energy. Its bound 12/(γλ) includes the projection, which does not commute with the weight. Passage through tests, graph closure, and strong multiplier convergence asserts no domain preservation by the weight. The TeX window above Ecore is not covered; see [the precise scope](CUSP_WEIGHTED_INVERSE.md).
`RadialCoreGroundChoice` proves that A004's positive radial witness also satisfies its original test gap, via simplicity of the actual eigenspace. The weighted chain retains this choice in `AtomicSchurReference` and the quantitative full-ground-state certificate. For the same vectors u,v, set η=v−cu=−cζ. `AtomicGroundWeightedResponse` proves ‖exp(κλT)η‖₂≤(12cλ/γ)‖exp(κλT)Wu‖₂, where W=p.potential−p.core. `SchurResponseEquation` also proves η's exact equation in the full domain, with forcing −cλ²Wu and term c(Efull−Ecore)u. Neither projection–weight commutation nor domain preservation by the weight is assumed.
`AtomicWeightedResidual` and `AtomicGroundWeightedDecay` eventually give ‖exp(κλT)η‖₂≤C exp(−dλ) and c∈[1/2,1], uniformly for κ in an interval fixed before λ. States are chosen before κ. The separate lemma `SchurNormalizationThreshold` also controls 1−c by the square of ζ's exponential bound; see [the proof and its limitations](ATOMIC_WEIGHTED_RESPONSE.md).
`AtomicGroundWeightedDecomposition` finally expresses these results using both actual smooth normalized eigenfunctions, the same positive reference, and the same correction η=ψfull−cφcore. Orthogonality and weighted mass ≤C² exp(−2dλ) are explicit. The response PDE holds pointwise by `AtomicResponseWavefunction`; this assembly asserts no pointwise estimate, fine rate, or holomorphic extension of η. The wrapper `CuspParameters.atomicGround_weighted_decomposition` also chooses cutoffs before coupling; it requires only `BasicConditions`, modulo A002+A004, without A003.
The [fine assembly](CUSP_FINE_FORCING.md) then retains the exact action and log-flat cost for this same response. Both terms of its [full right-hand side](ATOMIC_FINE_RESPONSE_DATA.md) are controlled in local L² after every fixed-order derivative, with only one cΓ factor. The [elliptic assembly](ATOMIC_RESPONSE_JETS.md) now supplies pointwise jets of η on the inner cusp neighborhood, bounded by CcΓλ⁴ exp(−λJ(Ecore,R)) exp(−β₁log²λ). A005 admits only the universal fixed-ball estimate; magnetic identities, uniform coefficients, and weight transport are proved. The manuscript's extra gauge is omitted because centers stay in a compact set and the ungauged coefficients are already uniformly bounded.
The [full scattered source](CUSP_SCATTERED_SOURCE.md) is now controlled for these same states and coefficients by multiplication by λ²W and Leibniz. Its semiclassical jets cost a polynomial λ⁶ and separately retain the global factor exp(−βglobal log²λ) and local profile logFlat βlocal tStar t exp(−κλt), on both closed supports, including tips. The margins are independent in (0,β).
The relative incoming integral, full active cell, and physical Schur errors o(A) are now established. The final connection uses the same source coefficients in opposite-support reconstruction and in the envelope. No holomorphic extension of η is claimed.

`LandauRadialEquation` proves the actual integral kernel's ODE, with two differentiations under the integral justified by Cauchy majorants and proper-time integration whose two boundary terms vanish. `LandauExteriorUniqueness` then proves that every real solution of this ODE in L²((a,∞),r dr) is ΓK. Caccioppoli deduces derivative integrability before the Wronskian argument; no derivative-energy hypothesis remains in this theorem. Positivity of the solution gives Γ>0. `RadialCoreExteriorState` now connects this uniqueness to the actual core eigenfunction: A004 supplies a classical positive radial choice, `MagneticRadialReduction` computes its equation, and `RadialPlaneL2` deduces radial integrability from the physical norm. This yields the exact identity φcore=ΓK, with Γ>0, on all r>r₀. See the [precise audit](RADIAL_EXTERIOR_KERNEL.md).

`RadialCoreProfileEstimates` now proves that the actual positive profile is decreasing and satisfies f(r)≥c>0 for 0≤r≤h, with constant and threshold before coupling and state. The proof uses the full ODE, exterior mass, and a quadratic flux comparison, without harmonic-profile convergence. `RadialCoreKernelComparison` then gives f(r)≤ΓK(r) for all r>0, using the coefficient from the same exterior identity. The compiled assembly `RadialCoreNormalizationLower` deduces Γ≥c h² and Γ⁻¹≤C h⁻² via A002+A004, without A003. This variant is weaker than h^(3/2) in Appendix B; it suffices where a free polynomial exponent is absorbed by a strictly positive exponential margin. Neither B.1 and its H²_loc/C⁰_loc convergence nor the literal h^(3/2) bound are claimed.

The auxiliary branch `LandauExteriorConvolution` → `RadialCoreSourceRepresentation` → `RadialLandauAverage` → `RadialCoreNormalization` compiles. It justifies pointwise representation outside the core and the exact polar identity for the same Γ, with explicit A003 for the representation. The normalized average profile equals 1 at zero; neither its positivity nor identification with a regular Green solution is assumed. See [the scope and uses of normalization](RADIAL_NORMALIZATION.md). The two exact kernel derivatives are not a differentiated asymptotic expansion.

## What is not claimed

`thm_main` is proved without its own `sorry`; its four classical dependencies A002–A005 are not formalized here and remain explicitly admitted. `elementaryPotential_main` establishes the conclusions for the literally fixed elementary potential. No original source, saddle, or tunneling estimate is added to these admissions.

The min–max levels `groundEnergy` and `secondEnergy` are identified with the minimum and maximum of the actual sector bottoms. Global eigenspaces and their gap are constructed; `OperatorMainConclusion.arbitrarily_large_operator_crossings` supplies arbitrarily large couplings where the L² ground eigenspace has dimension two and is isolated. This constructs neither an enumeration of the whole discrete spectrum, a projection onto a full window, nor a literal identification of each `parityEnergy` with Mathlib's inf σ. The operator content required for the three conclusions is supplied by the certificates and decompositions actually proved.

Alternation is expressed by two interlaced parameter sequences tending to infinity, where the ground state is simple and respectively even/odd. Multiplicity two is required at **every** sufficiently large min–max crossing, not just on the extracted sequence. No equality of the two zero sets is assumed. No spacing or uniqueness of zeros is claimed.
