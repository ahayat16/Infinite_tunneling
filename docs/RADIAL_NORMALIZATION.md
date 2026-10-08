# Exterior radial coefficient: a sufficient polynomial bound

**Status as of September 18, 2026:** the real profiles, full ODE, Wronskian comparison, Γ bounds in `RadialCoreNormalizationLower`, and auxiliary integral identities compile without additional admissions. Their use in the relative comparison of the seven inactive cells now compiles, first for the Gaussian envelope and then for the TeX complex-Hessian prefactor. The check at the historical relative-estimate milestone passed with 1843 admission-free theorems and 618 guards. Since then, the [relative parity errors](../InfiniteZero/CanonicalParityRelativeErrors.lean) and [final assembly](../InfiniteZero/ConstructedMainProof.lean) compile; [thm_main](../InfiniteZero/Remaining.lean) is proved modulo the two classical admissions A002 and A004.

## Result of the compiled assembly

Fix `b>0` and `p.r₀>0`. With the core data assembled from A002+A004 and the core realization A002, constants `c,C,T>0` are chosen before `λ`. For `λ≥T`, if `φ` is an actual normalized, real, radial, strictly positive core ground state, and **the same state** satisfies

\[
 \phi(x)=\Gamma K_{h}^{E_h}(|x|),\qquad |x|>r_0,
 \quad h=\lambda^{-1},\quad
 E_h=-h^2\,\texttt{atomicGroundEnergy}(b,p.core,\lambda),
\]

then

\[
 \Gamma>0,\qquad \Gamma\ge c h^2,\qquad
 \Gamma^{-1}\le C h^{-2}=C\lambda^2.
\]

The theorems `CuspParameters.exists_radialCore_coefficient_bounds_of_radialData` and `exists_radialCore_kernel_coefficient_bounds_of_radialData`, in [`RadialCoreNormalizationLower.lean`](../InfiniteZero/RadialCoreNormalizationLower.lean), express this bound for any given state and coefficient, and then an existential version preserving that same `φ` and `Γ` in the bounds and exterior identity. The wrapper `CuspParameters.radialCore_normalization_lower`, in `Remaining.lean`, supplies the classical inputs from `b>0` and `p.r₀>0`. Neither cusp parameters, L, nor A003 are needed for this bound. Positivity concerns the radial witness from A004, not the choice `canonicalAtomicState`.

## Proof from the physical objects

1. `RadialEigenfunctionEquation` computes the equation for `f(r)=realRadialProfile φ r` from the concrete Hamiltonian: for `r>0`, `(r f′)′=r q(r) f(r)`, where `q(r)=λ²(b²r²/4+coreRadialProfile r)−Ecore`. `CoreRadialMonotonicity` proves that this coefficient is increasing. `RadialGroundMonotonicity` uses positivity and integrability of `r f²` to deduce that `f` is decreasing on `[0,∞)`.
2. The classical energy bound `Ecore≤−λ²+Bλ` and passage through the closed graph give mass outside the core at most `B/λ`. For `λ≥2B`, the ball of radius `r₀` therefore contains at least half the mass. `RadialCenterLower` and monotonicity give `f(0)≥sqrt(1/(2πr₀²))`.
3. `RadialProfileLower` integrates two flux inequalities, using `q≥−λ²`, to obtain `f(r)≥f(0)(1−λ²r²/4)`. `RadialCoreProfileEstimates` deduces a constant `c₀>0`, chosen before `λ` and the witness `φ`, such that `f(r)≥c₀` for `0≤r≤h`. This result assumes no limit of the rescaled harmonic profile.
4. Set `K(r)=landauKernel b h E_h r` and `W(r)=r(f(r)K′(r)−f′(r)K(r))`. The two ODEs give exactly

   \[
     W'(r)=-\lambda^2 r\,v^\circ(r)f(r)K(r)\ge0.
   \]

   The core is nonpositive, and `f` and `K` are positive. The exterior identity `f=ΓK` implies `W=0` at every sufficiently large radius. Thus `W≤0` for all `r>0`, then `(f/K)′=−W/(rK²)≥0` and `f(r)≤ΓK(r)`. `RadialWronskianComparison` proves the general argument; `RadialCoreKernelComparison` checks its hypotheses for the actual states and kernels. Neither the behavior of the singular kernel at the origin nor a Green formula is used.
5. The already proved bound `K(r)≤1/(π E_h r²)`, applied at `r=h`, gives `c₀≤f(h)≤Γ/(π E_h h²)`. Since eventually `E_h≥1/2`, `Γ≥(c₀π/2)h²`. The reciprocal bound follows by positivity.

The conditional lemmas in this chain are admission-free. Their application to the actual core uses only A002 and A004, which include neither profile monotonicity nor a lower bound on Γ.

## Deliberate departure from Appendix B

The manuscript proves `Γ_h≥c h^(3/2)` after local harmonic convergence of the profile, Lemma B.1. The variant `Γ_h≥c h²` is weaker as `h→0`. It therefore proves **neither B.1 nor the literal power in Lemma B.2**. It suffices for the two specific uses of this normalization:

| Use in the TeX | Cost with the variant |
|---|---|
| L7.1, inactive cells, lines 6207–6273 | `1+Γ_h⁻²≤C h⁻⁴`, instead of `C h⁻³` |
| L8.2, core source, lines 6731–6770 | The missing factor `Γ_h` costs `C h⁻²`, instead of `C h^(-3/2)`; the factor `c_h⁻¹` separately requires `c_h≥1/2` |

In both cases the polynomial exponent `M` is free and the action margin is strictly positive. For every `a>0`, fixed `M`, and `C₀≥0`, `h^(-M) exp(C₀ log²(1/h)−a/h)` is eventually bounded by `exp(−a/(2h))`. Increasing `M` therefore preserves the intended conclusions. No upper bound on Γ is needed for this comparison. A lower bound on Γ alone does not close these applications: it must be combined with source and kernel estimates and then the saddle size. This assembly is now proved for the seven inactive cells, as detailed below. It does not by itself close application L8.2 or the active-cell asymptotic.

The ratio is now formalized in [RelativeNormalizationRatio](../InfiniteZero/RelativeNormalizationRatio.lean): `(Γ²+1)/Γ²≤Dλ⁴` and `(Γ²+1)/(c²Γ²)≤4Dλ⁴` for `c≥1/2`, with D and the threshold chosen before λ and **for every same state and its exact tail**. The universal result is `exists_radialCore_normalizationRatio_bound_of_radialData`. It applies directly to the φ and Γ already selected by the source profiles and [seven-cell bounds](INACTIVE_CELLS.md), without choosing a second state or exterior coefficient.

[ActiveSaddleEnvelope](../InfiniteZero/ActiveSaddleEnvelope.lean) uses the scalar size `logFlatSaddleLeadingSize` and defines exactly

\[
 \mathfrak a_{\rm G}
 =\varepsilon^2a_q^2c^2\Gamma^2\lambda^6\sqrt\lambda\,
 e^{-\lambda A_h}S_{\rm G}(\lambda^{-1})^2,
\qquad
 A_h=2J_b(E_h^\circ,R)+J_b(E_h,2L-R).
\]

In this comparison, `E_h°=−h² Ecore(λ)` and `E_h=−h² Efull(λ)`. The core and full-potential energies remain distinct and λ-dependent in A_h. The scalar slope `c*=α−iθ`, however, is fixed at limiting energy 1: `α=(J′_1(R)+J′_1(2L−R))/2`, `θ=√3 bL/2`. The factor `λ^6 * sqrt λ` is exactly λ to the power 13/2.

The ratio of the absolute bound to this envelope costs at most `C λ^(10+4−13/2) S_G⁻² exp(−31δλ)`. For λ≥1, the power is bounded by λ⁸. `SaddleNormalizationIdentity` absorbs this cost with **N=8** and the weakened margin `30δ`, leaving `exp(−15δλ)`. [AtomicInactiveRelative](../InfiniteZero/AtomicInactiveRelative.lean) deduces the seven individual bounds and the **sum of the seven norms**, for the actual constructed state and the canonical state, with the same φ, ψ, c, Γ and exact tail. The factor seven is absorbed into the constant; no upper bound on Γ is added.

The physical theorems retain only `c∈[1/2,1]` in their types: they give neither `c=waveInner φ ψ` nor a decomposition identity. The scalar comparison lemma holds for every real `c≥1/2`; this alone does not identify the existential c with the one in the active asymptotic. The assembly in [ConcreteChannelWitnesses](../InfiniteZero/ConcreteChannelWitnesses.lean) chooses the active witnesses and then applies the universal inactive bound to those same witnesses.

The Gaussian prefactor `S_G` uses `Re w`. The compiled module [SaddleEnvelopeComparison](../InfiniteZero/SaddleEnvelopeComparison.lean) also defines the actual complex prefactor using `1+w`, proves its norm identity with `S_TeX`, then `S_G²/S_TeX²=‖1+w‖/Re w→1` and eventually `0<S_TeX`, `S_TeX²≤S_G²≤2 S_TeX²`. The scalar comparison is therefore no longer an open obligation. [ActiveSaddleEnvelopeComparison](../InfiniteZero/ActiveSaddleEnvelopeComparison.lean) and [AtomicInactiveRelativeTex](../InfiniteZero/AtomicInactiveRelativeTex.lean) also compile: the same relative result uses the TeX complex-Hessian envelope, with an additional factor two in the constant, without changing the states or Γ. These conditional assemblies are admission-free; their wrappers use only A002 and A004. A003 does not enter this comparison.

The universal version accepting another actual positive radial state, its own exact tail, and an arbitrary real coefficient `c≥1/2` now compiles in [CanonicalInactiveRelative](../InfiniteZero/CanonicalInactiveRelative.lean). Uniqueness of the positive state and Γ aligns the tails; changing c costs at most four in the constant. The main active-cell asymptotic is a [separate result](ACTIVE_CHANNEL_ASYMPTOTIC.md); the final proof does not follow solely from the comparisons in this paragraph.

## Auxiliary convolution identities

A separate branch also compiles:

- `LandauExteriorConvolution` proves integrability and continuity of the convolution outside a ball containing the support, then turns almost-everywhere equality between continuous functions into pointwise equality.
- `RadialCoreSourceRepresentation` applies the universal contract `FreeLandauResolventKernel` to `−λ² core·φ`. The factors `λ²` and `h²` cancel exactly, giving `φ(x)=∫Kfree(x,y)(−core(y))φ(y)dy` outside the core. The free-kernel contract remains an explicit argument; its wrapper derives it from A002.
- `RadialLandauAverage` performs the polar change of variables with its Jacobian and justifies Fubini for the actual compactly supported source.
- `RadialCoreNormalization` sets `regularLandauProfile(R,s)=Re(radialFreeLandauAverage(R,s))/K(R)` and proves its value `1` at `s=0`, real integrability, and the identity `Γ=2π∫₀∞ s regularLandauProfile(R,s)(−coreRadialProfile(s))f(s)ds`. The exterior equality at this single radius `R>r₀` preserves the given Γ.

These identities do not claim to identify this profile with the regular solution of the radial Green problem, or to prove that it is at least `1` or independent of `R`. Its imaginary part is not assumed to vanish. This branch uses A002 for the physical representation; the Wronskian proof of the polynomial Γ bound is independent of it.
