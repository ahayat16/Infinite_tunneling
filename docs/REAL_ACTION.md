# Real action: proved calculations and analytic connections

`BridgeAction.lean` defines exactly the blueprint’s explicit formula:

\[
J(b,E,r)=\frac r4\sqrt{b^2r^2+4E}
+\frac Eb\operatorname{arsinh}\frac{br}{2\sqrt E}.
\]

For `b ≠ 0` and `E > 0`, Lean verifies without admissions:

- `J(0)=0` and `J'(r)=√(b²r²+4E)/2`;
- the eikonal identity `J'(r)²=E+b²r²/4`;
- strict increase and strict convexity on nonnegative radii;
- the formula `J''(r)=b²r/(2√(b²r²+4E))`;
- `J(r)=∫₀ʳ √(E+b²s²/4) ds`;
- `J(r)-J(s) ≥ √E(r-s)` for `s≤r`.

For `b>0` and `0≤s≤r`, the stronger bound

\[
J(r)-J(s)\ge\frac b4(r^2-s^2)
\]

is also proved. The squared geometric tip distances differ by `3R²`. `GeometryAction.lean` deduces the exact margin `3bR²/4` between same-cusp channels and the cross channel, for both signs and **every positive energy**. This bound is independent of `E`.

`BridgeActionMinimum` also proves the unique minimum of `H(τ)=Eτ+(br²/4)coth(bτ)` for `τ>0`, attained at `τ*=arsinh(br/(2√E))/b`, and its exact value `J`. `BridgeActionEnergy` proves `∂E J=τ*`.

`LandauKernel` defines the proper-time integral and proves convergence, positivity, and a global bound. `LandauKernelDecay`, followed by `LandauKernelUniform`, establishes without admissions:

\[
 h\log K_h^E(r)\longrightarrow -J_E(r),
\]

uniformly on every strictly positive compact rectangle in `(E,r)`, for fixed `b>0`. The bounds allowing arbitrary loss are uniform:

\[
 c h^{-2}e^{-(J+\eta)/h}\le K_h^E(r)
 \le C e^{-(J-\eta)/h}\quad(h>0).
\]

`LandauLaplaceTails` proves that the contribution outside a neighborhood of the minimum, multiplied by `exp(J/h)`, is uniformly exponentially small; it remains negligible after multiplication by every inverse power of `h`. `LandauLaplaceLeading` now establishes the prefactor:

\[
 h^{3/2}e^{J/h}K_h^E(r)\longrightarrow
 k_0=\frac{b}{4\pi\sinh(b\tau_*)}
       \sqrt{\frac{2\pi}{H''(\tau_*)}}>0.
\]

`LandauLaplaceUniformLeading` proves this limit **uniformly in `(E,r)` on every compact subset of the strictly positive quadrant**, for fixed `b>0`. The relative form `h^(3/2) exp(J/h) K / k₀ → 1` is also uniform. The proof first treats moving parameters `E→E₀>0`, `r→r₀>0` through Taylor expansion at the minimum, dominated convergence, and uniform tail control, then deduces compact uniformity. The differentiated expansion remains to be proved; the complex version on a shrinking window is described below. The kernel is the explicitly defined integral; its classical identification with the resolvent is isolated in A003, with a [reference and natural-language proof](CLASSICAL_LANDAU_RESOLVENT.md).

`ComplexLandauKernel` defines the same proper-time integral for complex radius `r`. If `Re(r²)>0`, the norm of its integrand is exactly the real integrand at radius `r_eff=sqrt(Re(r²))`. The modulus of `r` does not replace this effective radius. Integrability for `b,h,E>0`, exact agreement with the real kernel, and domination of every measurably restricted integral are proved. In particular, `|K_h^E(r)|≤K_h^E(r_eff)`.

`BridgeActionTaylor` establishes the global bound `|J(E,s)−J(E,r)−J′(E,r)(s−r)|≤(b/4)(s−r)²` for `b,E>0`. `ComplexLandauEffectiveRadius` and `ComplexLandauAction` deduce `J(E,r_eff)=J(E,r)+J′(E,r) Re δ+O(|δ|²)` uniformly on positive compact sets. `BridgeTimeRadial` controls movement of the critical time. These results transfer **all** tails, including proper time near zero, to the real problem (`ComplexLandauTails`).

`ComplexLandauLocalProfile` extracts the complex linear term exactly and proves uniform Gaussian domination. Together with the exact integral decomposition, `ComplexLandauAsymptotic` now establishes

\[
\frac{h^{3/2}e^{(J_E(r)+J'_E(r)\delta)/h}K_h^E(r+\delta)}{k_0(E,r)}
\longrightarrow1,
\qquad |\delta|\le M t_*h^{3/4},
\]

uniformly in `E,r` on positive real compact sets and in the indicated complex perturbation. The action retains the actual varying energy; it is not replaced by its limit. This proof admits no complex saddle method. It does not supply a differentiated asymptotic expansion on a fixed complex neighborhood. See the [detailed proof and its scope](SHRINKING_COMPLEX_KERNEL_PLAN.md).

Holomorphy of the parameter integral is now proved separately in `ComplexLandauHolomorphic`: for fixed `b,h,E>0`, the actual kernel is analytic on `Re(z²)>0`. The proof justifies differentiation under the integral through a local real majorant and a Cauchy estimate. This regularity does not supply a differentiated expansion uniform in `h`. `ComplexCuspKernelHolomorphic` deduces joint holomorphy of the three kernels composed with the charts, and their product, on a fixed geometric bidisk. This domain is common to bounded tangential parameters, all positive `b,h`, and all three strictly positive real energies; derivative estimates uniform in these parameters are not asserted.

`ComplexCuspKernelProfile` applies the result to the **three complex cusp-chart radii**. With base radii `R,R,D=2L−R`, the linear normalization terms are respectively `J′_E(R)t/2`, `J′_E(R)u/2`, and `J′_E(D)(t+u)/2`. The quotients normalized by `k₀` tend to `1` for `E→E₀>0`, bounded tangential parameters, and `|t|,|u|≤M tStar h^(3/4)`. The required quadratic remainders come from the actual charts; no analytic remainder is assumed. The field, geometric parameters, and window constant remain fixed in these moving-parameter theorems.

`ComplexCuspPhase` extends the magnetic phase by its actual polynomial and proves `Φcomplex=Φ*+θ(t+u)+RΦ`, with `θ=√3 bL/2` and `|RΦ|≤C(|t|²+|u|²)` uniformly for bounded tangential parameters on a small bidisk. This gives `exp(i RΦ/h)→1` on the same window. These steps concern the kernels and geometric factor. The [atomic profiles](CUSP_SOURCE_PROFILES.md) and [physical active-cell asymptotic](INCOMING_PHYSICAL_ASYMPTOTIC.md) are now established separately, then used in the channels and [final proof](../InfiniteZero/Remaining.lean), modulo A002–A004.

`ConstructionCuspBounds` and `GeometryActionSlopes` establish tip slopes and outgoing inequalities on the closed supports. After a uniform separation choice (`SeparationCertificate`), `InactiveSupportGaps` proves the margins of every inactive pair: `32δ` for core/core and the four mixed pairs, `48δ` for the two same-cusp pairs, where `δ=bR²/64`. The two energies remain distinct: `E>0` and `0<E₀≤2`. Converting these margins into smallness relative to the actual active envelope additionally requires control of atomic sources and their normalizations.

One cell is already fully controlled in absolute value. By Cauchy–Schwarz, `CoreSourceBound` proves `‖F₀‖₁ ≤ h⁻² √(∫core²)` for every normalized state. `InactiveKernelBounds` bounds the pairing by `h²` times the kernel supremum and both L¹ norms. Their combination in `CoreCellBound.exists_coreCell_exp_bound` gives

\[
 |I_{00}(h)|\le C h^{-2}
 e^{-(A_*(L,E,E_0)+32\delta-\eta)/h},
 \qquad A_*=2J_{E_0}(R)+J_E(2L-R).
\]

After choosing `L`, the constant is uniform in `h>0`, the normalized atomic state, `E` in a positive compact set, and `0<E₀≤2`. Smallness **relative to the active envelope** additionally requires control of that envelope and its normalization; this step is not part of the absolute bound.
