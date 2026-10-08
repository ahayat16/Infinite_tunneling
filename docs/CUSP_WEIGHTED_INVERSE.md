# Compressed inverse with the exact cusp weight

**Status as of September 18, 2026: Lean proof compiled and global audit passed.** This document audits the statement and natural-language proof of [`AtomicCuspWeightedInverse.lean`](../InfiniteZero/AtomicCuspWeightedInverse.lean). `bash scripts/check.sh` passed: full build, `assert_no_sorry` guards, transitive axiom export, and dependency regeneration. The inputs are radial spectral data and explicit operator realizations; no new weighted-inverse admission is introduced. This result alone does not close `thm_main`.

## Exact statement and order of choices

Fix `p`, `hp : p.BasicConditions`, `hRad : RadialCoreSpectralData p.b p`, core and full-potential realizations at all couplings, and `χ : CuspWeightCutoffs p`. Existence of these cutoffs is proved by `exists_cuspWeightCutoffs hp`; their structure is not an uninstantiated analytic hypothesis.

Write `T=χ.weight`, `γ=hRad.gap>0`,

\[
A_\lambda=\operatorname{magneticOperator}(p.b,\lambda,p.potential),
\qquad E_0(\lambda)=\operatorname{atomicGroundEnergy}(p.b,p.core,\lambda).
\]

The theorem `CuspParameters.exists_atomic_cusp_weighted_inverse_of_radialData` establishes the following order:

\[
\exists M>0,\ 0\le T\le M,\quad
\exists\kappa_0>0,\ \exists N>0,\quad
\forall\lambda\ge N,\ \exists\phi_\lambda,\ \exists v_\lambda,\quad
\forall E\le E_0(\lambda),\ \exists R_E,\quad
\forall\kappa\in[0,\kappa_0].
\]

Here `φλ` is an actual smooth normalized core ground state; `vλ∈D(Aλ)` represents **that same state** in `L²` and has norm one. Set `Q=1−vλ⟨vλ,·⟩`, `B=orthogonalCompression Aλ vλ`, `Wκ=exp(κλT)`, and `W−κ=exp(−κλT)`, as actual `L²` multipliers. Then `R_E` is an actual resolvent of `B` at energy `E`, and

\[
\left\|W_\kappa\,\iota\,R_E\,Q\,W_{-\kappa}\right\|_{L^2\to L^2}
\le \frac{12}{\gamma\lambda}.
\]

`ι` is the inclusion of `vλ⊥` into `L²`. The left-hand side is exactly `weightedProjectedResolvent`, including the projection. Constants precede `λ`; the reference `φλ`, its class, and the compression precede `E` and `κ`. The resolvent chosen at a given energy also precedes `κ`. None of these objects depends on the double-well separation `L`. The stated uniformity concerns these variables for fixed parameters `p` and cutoffs, not a varying family of geometries.

## Semiclassical convention and scope restriction

For `h=λ⁻¹`, the manuscript operator is `H_h=h²Aλ`. If `e=h²E`,

\[
[Q(H_h-e)Q]^{-1}=h^{-2}[Q(A_\lambda-E)Q]^{-1}.
\]

The bound `12/(γλ)` therefore becomes `12/(γh)` for the semiclassical resolvent; the weight is exactly `exp(κT/h)`. This scaling conversion is explained here in natural language, rather than asserted as a new Lean theorem about rescaled operators.

The result covers **the entire half-line `E≤Ecore`**. The manuscript, [`lem:weighted-inverse` and LA.2](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L6950), states a symmetric window around the core energy. The portion of that window **above** `Ecore` is not covered here. The variant suffices for application at the full atomic energy, since `Efull≤Ecore` is already proved. It should not be presented as a formalization of the entire TeX window.

## Weight and smooth approximations

[`CuspWeight.lean`](../InfiniteZero/CuspWeight.lean) constructs

\[
T(x)=\chi_+(x)(\nu_+(x))_++\chi_-(x)(\nu_-(x))_+,
\qquad t_+=\max(t,0).
\]

The cutoffs are smooth, compactly supported, between zero and one, equal to one on the closed support of their cusp, and zero on the other cusp and on the ball `‖x‖≤4r₀`. The weight is compactly supported, nonnegative, and Lipschitz. On each cusp support it equals the normal coordinate `t` exactly. The proof does not require the supports of the two cutoffs to be disjoint everywhere outside the cusps.

[`SmoothPositivePart.lean`](../InfiniteZero/SmoothPositivePart.lean) replaces `t+` with `sε(t)=(t+√(t²+ε²))/2`. For `ε>0`, this function is smooth, with `0≤sε−t+≤ε/2` and `0≤sε′≤1`. [`CuspWeightApproximation.lean`](../InfiniteZero/CuspWeightApproximation.lean) retains the cutoffs and obtains weights `Tε` satisfying, for `0<ε≤1`,

\[
0\le T_\varepsilon-T\le\varepsilon,
\quad T_\varepsilon=0\text{ on }\{\|x\|\le4r_0\},
\quad 0\le T_\varepsilon\le M,
\quad |\nabla T_\varepsilon|^2\le G,
\]

with `M,G>0` independent of `ε`. Vanishing near the core comes from the cutoffs, not the smoothed positive part, which is strictly positive. Choosing `κ≤1/√(8G)` gives `|∇(κλTε)|²≤λ²/8`, uniformly in `ε`.

## Identity on tests, then graph closure

For a smooth compactly supported test `ψ` and a smooth real weight `F`, `magneticForm_exp_test`, in [`MagneticWeightedTest.lean`](../InfiniteZero/MagneticWeightedTest.lean), proves

\[
q_{A_\lambda}(e^F\psi)
-\int |\nabla F|^2|e^F\psi|^2
=\Re\langle e^F\psi,e^FA_\lambda\psi\rangle.
\]

The correction coefficient is **one**, by the exact product identity and integration by parts. All integrability statements follow from compact support of the test.

`AtomicWeightedTestCoercivity` reserves half the exterior coercivity `λ²/4` for the weight cost. More precisely, it accepts any continuous `P` with `P≤(λ²/8)χout²`. Since `F=0` on the ball of radius `4r₀` and `χout=1` from radius `3r₀` onward, `P=|∇F|²` satisfies this contract. IMS localization and the radial gap give, after a uniform threshold,

\[
\frac{\gamma\lambda}{2}\|W u\|^2
-2\gamma\lambda|\langle v_\lambda,Wu\rangle|^2
\le \Re\langle Wu,W A_\lambda u\rangle-E_0\|Wu\|^2.
\tag{1}
\]

[`AtomicSmoothWeightedGraph.lean`](../InfiniteZero/AtomicSmoothWeightedGraph.lean) and [`MagneticWeightedGraph.lean`](../InfiniteZero/MagneticWeightedGraph.lean) first transfer this inequality from tests to `D(Aλ)`. Each side is continuous in the two coordinates `(u,Aλu)` of the closed graph, for the fixed bounded multiplier. **Membership of `Wu` in the operator domain is not assumed.** Nor is a previously established global form identity for a Lipschitz weight required.

Taking `εn=1/(n+1)` then gives (1) for the exact weight `Wκ`. `BoundedMultiplierLimits.tendsto_boundedPotentialMul_apply` uses almost-everywhere identifications and dominated convergence of `∫|(Wn−Wκ)u|²` for each `u∈L²`. The weight majorant is uniform in n for fixed λ,κ; it may depend on those two parameters. Weighted inner products pass to the strong limit. No uniform convergence of derivatives is used. This assembly is in [`AtomicCuspWeightedGraph.lean`](../InfiniteZero/AtomicCuspWeightedGraph.lean).

## Unweighted resolvent and the same radial reference

Specializing (1) to `κ=0`, for `u⊥vλ`, gives `B≥E0+γλ/2`. `OrthogonalCompression` supplies self-adjointness on the exact domain `{u∈vλ⊥ | u∈D(Aλ)}`; `CoerciveResolvent` then constructs an actual resolvent `R_E` for every `E≤E0`. Its existence precedes the weighted estimate, without circular reasoning.

`AtomicPerturbationDomain` transports **the same** radial ground state into `D(Aλ)` and provides

\[
A_\lambda v_\lambda=E_0v_\lambda+r_\lambda,
\qquad r_\lambda=\lambda^2(p.potential-p.core)v_\lambda.
\]

The global Agmon tail and perturbation support give `‖rλ‖≤Kλexp(−dλ)` (`AtomicResidualDecay`). The weight support avoids the ball of radius `4r₀`; reducing `κ₀` once and for all, `AtomicWeightedTail` gives, uniformly for `0≤κ≤κ₀`,

\[
\delta_\lambda:=\|(W_\kappa-I)v_\lambda\|
\le C e^{-c_T\lambda},\qquad
\|W_\kappa v_\lambda\|\le1+C e^{-c_T\lambda}.
\]

Both estimates apply to every normalized radial ground state, so they can be used for the one already chosen in (1), without changing the reference or its phase.

## Lifting, absorption, and the constant twelve

For `ζ∈D(B)`, set `f=(B−E)ζ`. The exact lifting in [`WeightedCompression.lean`](../InfiniteZero/WeightedCompression.lean) is

\[
(A_\lambda-E)\zeta=f+\langle r_\lambda,\zeta\rangle v_\lambda.
\]

The inner-product convention is linear in the second variable. Symmetry of the real multiplier and `ζ⊥vλ` also give

\[
|\langle v_\lambda,W_\kappa\zeta\rangle|
=|\langle(W_\kappa-I)v_\lambda,\zeta\rangle|
\le\delta_\lambda\|W_\kappa\zeta\|,
\]

since `Wκ≥1`. Cauchy–Schwarz controls the residual term by `‖rλ‖‖Wκvλ‖‖Wκζ‖²`. `WeightedResidualAbsorption` chooses the threshold before `λ,κ,E` to ensure

\[
\frac{\gamma\lambda}{4}
+2\gamma\lambda\delta_\lambda^2
+\|r_\lambda\|\|W_\kappa v_\lambda\|
\le\frac{\gamma\lambda}{2},\qquad
\|W_\kappa v_\lambda\|\le2.
\]

`WeightedCompressedEstimate.weighted_compression_resolvent_bound` deduces

\[
\|W_\kappa R_E f\|\le\frac4{\gamma\lambda}\|W_\kappa f\|
\qquad(f\in v_\lambda^\perp).
\]

For arbitrary data `G∈L²`, it remains to insert `f=QW−κG`. The actual multipliers satisfy `WκW−κ=I` and `‖W−κG‖≤‖G‖`. `WeightedProjectedResolvent` then uses

\[
W_\kappa QW_{-\kappa}G
=G-\langle v_\lambda,W_{-\kappa}G\rangle W_\kappa v_\lambda,
\qquad
\|W_\kappa QW_{-\kappa}G\|\le3\|G\|.
\]

The product of `4/(γλ)` and `3` gives `12/(γλ)`. The projection is never assumed to commute with the weight, nor is its range assumed to be preserved by the weight. The exact norm formula for a rank-one operator is not needed for this upper bound.

## Classical dependencies and subsequent steps

The conditional theorem exposes `hRad`, `hAcore`, and `hApot`. Classical interfaces A004 and A002 supply these inputs; A003, identifying the free Landau kernel, does not enter this proof. Construction of the cutoffs, cusp-specific estimates, compression, and all absorptions remain Lean proofs in the project.

Application to the same Schur correction is now proved in `AtomicGroundFineResponse`. The exact tail of the same positive radial ground state supplies Γ; `AtomicCuspFineForcing` controls the actual forcing by

\[
\|e^{\kappa T/h}W\phi_{\rm core}\|_2
\le C\Gamma h^{-2}e^{-J_b(E_{\rm core,h},R)/h}
e^{-\beta_1\log^2(1/h)},\qquad 0<\beta_1<\beta.
\]

Here `W=p.potential−p.core`, including ε, and `Ecore,h=−λ⁻²Ecore`. The inverse is evaluated at the full energy, whereas the action in this forcing retains the core energy. The exact response coefficient `12cλ/γ` gives

\[
\|e^{\kappa T/h}\eta\|_2
\le Cc\Gamma h^{-3}e^{-J_b(E_{\rm core,h},R)/h}
e^{-\beta_1\log^2(1/h)}.
\]

The constants are fixed before λ, and the same states, `c∈[1/2,1]`, and Γ precede κ. `AtomicEnergyShiftForcing` also retains just one forcing factor: `c≥1/2` implies `‖ζ‖²≤3`, hence `‖ζ‖≤2`, and the scalar equation gives `|λ⁻²(Efull−Ecore)|≤3‖exp(κλT)Wφcore‖₂`. The [fine forcing proof and its scope](CUSP_FINE_FORCING.md) detail these applications, with no new admission and only A002+A004. `AtomicGroundFineDecomposition` also compiles: it chooses the same actual wavefunctions, retains the exterior tail with coefficient Γ, orthogonality, and the pointwise PDE, and bounds the weighted mass by the square of the fine estimate. The wrapper `CuspParameters.atomicGround_fine_weighted_decomposition` supplies the classical inputs from `BasicConditions` and `0<β₁<β`. The global check of the new assembly passed; A002+A004 are exactly the admissions found in the wrapper's dependencies.

The exact radial tail and sufficient bound Γ≥c h² are also [proved](RADIAL_NORMALIZATION.md); the fine harmonic profile of B.1 is not claimed. The [forcing derivatives](CUSP_FORCING_DERIVATIVES.md) are now bounded at every fixed order; the [full right-hand side](ATOMIC_FINE_RESPONSE_DATA.md) satisfies the same local bounds without an additional Γ factor. The [elliptic assembly](ATOMIC_RESPONSE_JETS.md) then supplies pointwise correction jets using the proved interior estimate, and the [full scattered-source profile](CUSP_SCATTERED_SOURCE.md) is assembled by Leibniz. At this milestone, the active integral and physical double-well spectral reduction remained to be completed; [L¹ integration of the profiles](CUSP_SOURCE_L1.md) was already proved. The weighted window remains limited to `E≤Ecore`, as stated above.
