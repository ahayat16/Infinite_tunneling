# The exterior radial kernel: ODE, integrability, and uniqueness

This document describes the analytic block of `prop:exact-radial-tail` and its P2.4 sublemmas: `landauKernel`, defined by an actual integral, uniqueness of the exterior radial L² branch, and their connection to the actual positive radial core ground state. The resulting exterior identity is `φcore(x) = Γ K(‖x‖)`, with `Γ > 0`, for every sufficiently large coupling. The positive radial choice follows from A002+A004 through the proved radial assembly; Hamiltonian reduction, polar coordinates, and kernel identification are separate Lean proofs. This uniqueness block contains no quantitative bound on Γ; the [additional bound `Γ≥c h²`](RADIAL_NORMALIZATION.md) is now proved in a separate assembly, with A002+A004.

The scalar-block modules, including [RadialExteriorEnergy.lean](../InfiniteZero/RadialExteriorEnergy.lean) and [LandauExteriorUniqueness.lean](../InfiniteZero/LandauExteriorUniqueness.lean), compiled without admissions. `bash scripts/check.sh` passed: full build, `assert_no_sorry` guards, transitive axiom export, and regeneration of the inventory and dependency graph. The new connection to the actual state in [RadialCoreExteriorState.lean](../InfiniteZero/RadialCoreExteriorState.lean) compiled without warnings. Its wrapper in [Remaining.lean](../InfiniteZero/Remaining.lean) also compiled during the full build with `Verification` (3725 jobs). Transitive axiom export and the inventory then succeeded: `scripts/check.sh` completed without error. The conditional assembly introduces no admission; the wrapper depends on classical contracts A002+A004.

For fixed parameters `b,h,E > 0`, set

\[
 I(r,\tau)=\frac{1}{\sinh(b\tau)}
 \exp\!\left[-\frac{E\tau+(br^2/4)\coth(b\tau)}h\right],
 \qquad
 K(r)=\frac{b}{4\pi h^2}\int_0^\infty I(r,\tau)\,d\tau.
\]

For `r > 0`, convergence and strict positivity are proved in [LandauKernel.lean](../InfiniteZero/LandauKernel.lean). The results in this document do not use the free-resolvent identity (formerly A003). They do not concern the singular radius `r = 0`.

The pointwise calculation in [LandauIntegrandODE.lean](../InfiniteZero/LandauIntegrandODE.lean) gives, with `s(τ) = b coth(bτ)/(2h)`,

\[
 \partial_r I=-s(\tau)rI,\qquad
 \partial_r^2 I=(s(\tau)^2r^2-s(\tau))I,
\]

then the exact identity, including its sign and factor in h,

\[
 -h^2\bigl(\partial_r^2 I+r^{-1}\partial_r I\bigr)
 +(b^2r^2/4+E)I=-h\,\partial_\tau I.
\]

Interchanges of radial derivatives and integration are justified in [LandauRadialDerivatives.lean](../InfiniteZero/LandauRadialDerivatives.lean). The complexified kernel has a local integrable majorant in the domain `Re(z²) > 0`, established by [ComplexLandauHolomorphic.lean](../InfiniteZero/ComplexLandauHolomorphic.lean). On nested discs around a positive radius, Cauchy's inequality is applied twice: first to the holomorphic integrand, then to its derivative. This gives integrable majorants for both derivatives, uniform in a neighborhood of the radius considered. The dominated differentiation theorem applies twice. The public lemmas `hasDerivAt_landauKernel` and `hasDerivAt_deriv_landauKernel` give the exact derivative formulas under the integral.

In [LandauProperTimeEndpoints.lean](../InfiniteZero/LandauProperTimeEndpoints.lean), the integrand tends to zero as `τ → 0+` and `τ → ∞`. At the first endpoint, setting `y = 1/sinh(bτ)`, the factor `y exp(−c y)` tends to zero for `c > 0`; it absorbs the `1/sinh(bτ)` singularity. At the second endpoint, a bound by a constant times `exp(−Eτ/h)` suffices. The Lean definition of the integrand at `τ = 0` is zero and agrees with its right limit.

[LandauProperTimeIntegral.lean](../InfiniteZero/LandauProperTimeIntegral.lean) deduces integrability of `∂τ I` from the pointwise identity above and integrability of I, ∂r I, and ∂r² I. The fundamental theorem of calculus on the half-line then gives

\[
 \int_0^\infty \partial_\tau I(r,\tau)\,d\tau=0.
\]

This step assumes neither integrability of the time derivative nor the kernel's Green equation. The assembly in [LandauRadialEquation.lean](../InfiniteZero/LandauRadialEquation.lean) proves `landauKernel_radial_ode`:

\[
 -h^2\bigl(K''(r)+r^{-1}K'(r)\bigr)+(b^2r^2/4+E)K(r)=0
 \qquad(r>0).
\]

Exterior integrability with radial measure `r dr` requires less than a Gaussian estimate. The already proved bound `landauKernel_le` gives

\[
 0<K(r)\le\frac1{\pi E r^2},\qquad
 r|K(r)|^2\le\frac1{(\pi E)^2}r^{-3}.
\]

For any `a > 0`, the majorant is integrable on `(a,∞)`. This proves `integrableOn_radial_landauKernel_sq` in [LandauRadialL2.lean](../InfiniteZero/LandauRadialL2.lean). Real continuity of the kernel is deduced there from its complex restriction. This is integrability at fixed parameters, with no assertion of differentiated expansions to all orders or bounds on a normalization factor.

For uniqueness, [RadialWronskian.lean](../InfiniteZero/RadialWronskian.lean) uses the explicit system `IsRadialODESolutionOn q f df a`:

\[
 f'=df,\qquad (df)'=q(r)f-r^{-1}df\quad\text{on }(a,\infty).
\]

Two solutions `(f,df)` and `(g,dg)` of the same system satisfy

\[
 W(r)=r\bigl(f(r)dg(r)-df(r)g(r)\bigr),\qquad W'(r)=0.
\]

The Wronskian is therefore constant throughout the interval. Its bound

\[
 |W(r)|\le\tfrac r2\bigl(f(r)^2+df(r)^2+g(r)^2+dg(r)^2\bigr)
\]

shows that this constant is integrable whenever all four energies are integrable on a tail `(R,∞)`, with `R ≥ a`. An integrable constant on a set of infinite measure is zero. This avoids choosing a sequence at infinity. `radialWronskian_eq_zero_of_integrable_tail` concludes `W = 0` on all of `(a,∞)`, even when integrability begins only at R. If `g > 0`, the derivative of f/g is then zero, so the ratio is constant throughout that interval.

Derivative integrability is not an input of the final L²-branch statement. To deduce it, assume q continuous and nonnegative. [RadialCaccioppoli.lean](../InfiniteZero/RadialCaccioppoli.lean) applies the fundamental theorem of calculus to the flux `r χ² f df` on a closed interval `[l,u] ⊂ (a,∞)`, with `χ(l) = χ(u) = 0`. A derivative identity and completion of the square give

\[
 \int_l^u r\chi^2(df)^2\,dr
 \le4\int_l^u r(\chi')^2f^2\,dr.
\]

All integrability statements on this finite interval follow from the continuity hypotheses; no global energy is assumed. [RadialExteriorCutoffs.lean](../InfiniteZero/RadialExteriorCutoffs.lean) constructs smooth cutoffs χn, zero at a+1 and a+n+3, equal to one on `[a+2,a+n+2]`, with `|χn′| ≤ D` independently of n. Their transitions have fixed width. Unlike the TeX variant with exterior gradient `O(1/R)`, only a uniform bound is needed here.

Indeed, Caccioppoli gives

\[
 \int_{a+2}^{a+n+2}r(df)^2\,dr
 \le4D^2\int_a^\infty rf^2\,dr.
\]

The integrability criterion using uniform integral bounds on increasing intervals gives finite derivative energy on `(a+2,∞)`. This is `IsRadialODESolutionOn.integrableOn_radial_deriv_sq` in [RadialExteriorEnergy.lean](../InfiniteZero/RadialExteriorEnergy.lean). It claims no derivative integrability up to boundary a.

For the Landau kernel, `q(r) = (b²r²/4 + E)/h²` is continuous and positive. The assembly in [LandauExteriorUniqueness.lean](../InfiniteZero/LandauExteriorUniqueness.lean) applies the energy estimate to f and K, then the Wronskian argument on their common tail. The statement `exists_eq_mul_landauKernel_of_radialODE` is exactly:

\[
 \begin{gathered}
 b,h,E,a>0,\qquad
 f''=\frac{b^2r^2/4+E}{h^2}f-r^{-1}f',\qquad
 \int_a^\infty rf(r)^2\,dr<\infty
 \\
 \Longrightarrow\quad
 \exists\Gamma\in\mathbb R,\quad
 f(r)=\Gamma K(r)\quad\text{for every }r>a.
 \end{gathered}
\]

The zero solution is allowed and gives `Γ = 0`. Since `K > 0`, Γ has the sign of the represented profile: `Γ > 0` is equivalent to strict positivity of f in the exterior. The Lean corollary `exists_pos_eq_mul_landauKernel_of_radialODE` supplies the positive coefficient when positivity of f is given. This uniqueness lemma alone asserts no quantitative bound on Γ or regularity of its h-dependence.

The connection to the actual state uses the field `positive_radial_ground` of [RadialCoreSpectralData.lean](../InfiniteZero/RadialCoreSpectralData.lean). For every λ beyond the contract threshold, it supplies a normalized ground state φ satisfying `IsPositiveRadial φ`. In [RealRadialState.lean](../InfiniteZero/RealRadialState.lean), this property means pointwise

\[
 \varphi(x)=f(\|x\|)\in\mathbb R,\qquad
 \operatorname{Re}\varphi(x)>0,\qquad
 f(r)=\operatorname{Re}\varphi(r e_1).
\]

This positive choice originates in Theorem 1.1(2) of Helffer–Kachmar, arXiv:2208.13030v5, and is transferred to the core by `RadialCoreSpectralAssembly`; references and scaling are detailed in [RADIAL_HARMONIC_CONTRACT.md](RADIAL_HARMONIC_CONTRACT.md). It assumes neither the exterior ODE, a polar identity, nor the Γ K formula. The positive witness may differ from the witness in the same contract's `ground` field. No positive phase for the arbitrary choice `canonicalAtomicState` follows directly.

Two independent calculations connect this state to scalar uniqueness:

- [MagneticRadialReduction.lean](../InfiniteZero/MagneticRadialReduction.lean) expands both covariant derivatives of the concrete Hamiltonian. For a real radial profile and `x ≠ 0`, angular terms cancel and `magneticHamiltonian_radial` gives `−f″(r) − r⁻¹ f′(r) + (b²λ²r²/4 + λ²V(x)) f(r)`. Outside the core, `V = 0`. The eigenvalue equation therefore gives exactly the ODE for K with `h = λ⁻¹` and `E = −(λ⁻¹)² * atomicGroundEnergy b p.core λ`.
- [RadialPlaneL2.lean](../InfiniteZero/RadialPlaneL2.lean) uses `planeCartesianEquiv_measurePreserving`, Mathlib's polar change of variables with Jacobian r, and the strictly positive measure of the angular interval. The lemma `integrableOn_exterior_radial_sq_of_representation` deduces from `MemLp φ 2 volume` and `φ(x) = f(‖x‖)` that `r f(r)²` is integrable on every `(a,∞)`, `a > 0`. It requires neither extra profile continuity nor prior integrability of its derivative energy.

The assembly in [RadialCoreExteriorState.lean](../InfiniteZero/RadialCoreExteriorState.lean) is `IsAtomicGroundState.exists_pos_radialCore_kernel`: for every actual positive radial ground state with negative reduced energy, the preceding uniqueness gives the pointwise identity on all `‖x‖ > r₀` with `Γ > 0`. The theorem `CuspParameters.exists_radialCore_kernel_of_radialData hb hr hRad` first chooses

\[
 T=\max\bigl(\texttt{hRad.threshold},\,2\,\texttt{hRad.energyBound}\bigr)>0.
\]

For `λ ≥ T`, the common energy bound `eλ = λ⁻² atomicGroundEnergy b p.core λ ≤ −1+B/λ ≤ −1/2` ensures `Eλ = −eλ > 0`. The result is then exactly

\[
 \forall\lambda\ge T,\quad
 \exists\varphi_\lambda\text{ a normalized positive radial ground state},\quad
 \exists\Gamma_\lambda>0,\quad
 \forall\|x\|>r_0,\qquad
 \varphi_\lambda(x)=\Gamma_\lambda
 K_{b,\lambda^{-1},E_\lambda}(\|x\|).
\]

Only `b > 0`, `p.r₀ > 0`, and the classical radial data are needed; no cusp or well-separation condition enters. The wrapper `CuspParameters.radialCore_kernel hb hr`, in [Remaining.lean](../InfiniteZero/Remaining.lean), supplies the data via A002+A004. It does not use A003. No new ODE, polar-measure, or exterior-tail admission is introduced.

This identity concerns the positive choice of core ground state. `RadialCoreNormalizationLower` now complements it with `Γλ≥c λ⁻²` and `Γλ⁻¹≤Cλ²`, using the full ODE, mass, and a Wronskian comparison; see [the proof and its scope](RADIAL_NORMALIZATION.md). The [spatial jets and source profiles](CUSP_FORCING_DERIVATIVES.md), then their [connection to the tunneling channels](ACTIVE_CHANNEL_ASYMPTOTIC.md), are now proved. Coupling regularity of state choices is not asserted here and is unnecessary for the [final proof](../InfiniteZero/Remaining.lean), compiled modulo A002 and A004. The manuscript's power h^(3/2) and local harmonic convergence are not claimed.
