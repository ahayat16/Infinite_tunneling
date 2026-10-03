# Derivatives of cusp forcing

This block extends the [undifferentiated forcing](CUSP_FINE_FORCING.md). It concerns derivatives of the actual product `Wφ`, where `W=p.potential−p.core`, and retains the coefficient `Γ` of that same state. The exponential weight multiplies **after** differentiation: the Lipschitz weight is never differentiated.

The pointwise and L² assembly is proved without a new analytic admission. Application to the actual core state uses only A002 and A004. It does not depend on free-resolvent identification A003 or the final theorem `thm_main`.

The analytic theorems of this block, including the finite sum applied to actual states under explicit radial data, use only standard Lean axioms. Their connection to the final theorem is now assembled in [ConstructedMainProof](../InfiniteZero/ConstructedMainProof.lean).

## Log-flat margin for each fixed order

Fix `0<β₁<β₂<β`. Profile derivatives are finite sums of terms `t⁻ᵐ P(log(t*/t)) exp(−β log²(t*/t))`. The exact factorization

\[
 t^{-m}P(\ell)e^{-\beta\ell^2}
 =\bigl(t^{-m}P(\ell)e^{-(\beta-\beta_2)\ell^2}\bigr)
   e^{-\beta_2\ell^2}
\]

and continuity of the first factor, extended by zero at `t=0`, give a uniform bound on `[0,t₀]`. [`LogFlatDerivativeLoss`](../InfiniteZero/LogFlatDerivativeLoss.lean) proves this assertion, including for each profile derivative. The constant depends on the fixed order; no uniformity in that order is needed.

[`CuspKernelJetBounds`](../InfiniteZero/CuspKernelJetBounds.lean) then proves the bound for every Fréchet jet of the two-dimensional profile. In particular, the normal derivative replaces the tangential cutoff `g(s)` with `s g'(s)`, still smooth and compactly supported. Induction therefore retains a stable profile family, without introducing an unbounded tangential factor. [`ConstructionCuspJetBounds`](../InfiniteZero/ConstructionCuspJetBounds.lean) applies this bound to the real affine charts and cutoffs of our potential. Thus, on the whole plane,

\[
 \|D^j q_\pm(x)\|\le A_j\,
    \operatorname{logFlat}_{\beta_2}(t_\pm(x)).
\]

Tips and support boundaries are included; outside the closed support all jets vanish.

## Kernel derivatives with exact action

On the complex disk centered at `r>0` with radius `h`, the effective real radius `s=√Re(z²)` satisfies `|s−r|≤2h`, uniformly on a fixed annulus. The radial action derivative is bounded there, hence `|J(E,s)−J(E,r)|≤Ah`. The already-proved complex majorant and real exact-action bound give

\[
 \sup_{|z-r|\le h}|K(b,h,E,z)|
 \le C h^{-2}e^{-J_b(E,r)/h}.
\]

Cauchy’s inequality on this disk then gives

\[
 |\partial_r^j K(b,h,E,r)|
 \le j!\, C h^{-(j+2)}e^{-J_b(E,r)/h}.
\]

The constants and threshold are uniform in `E,r` on the fixed positive rectangle, and are even chosen before `j` in this radial bound. See [`ComplexLandauSmallDisk`](../InfiniteZero/ComplexLandauSmallDisk.lean) and [`ComplexLandauDerivativeBounds`](../InfiniteZero/ComplexLandauDerivativeBounds.lean). Restriction of the complex derivative to the real axis is proved at every order.

The Euclidean norm is smooth with bounded jets on an annulus avoiding the origin. Mathlib’s composition rule gives spatial derivatives. For each fixed `n` and `h≤1`,

\[
 \|D^j[K(b,h,E,\|\cdot\|)](x)\|
 \le C_n h^{-(n+2)}e^{-J_b(E,\|x\|)/h},\qquad j\le n.
\]

See [`RadialCompositionJetBounds`](../InfiniteZero/RadialCompositionJetBounds.lean) and [`LandauSpatialDerivativeBounds`](../InfiniteZero/LandauSpatialDerivativeBounds.lean). Finally, [`ExteriorRadialJetBounds`](../InfiniteZero/ExteriorRadialJetBounds.lean) uses `φ=ΓK` on the open exterior of the core to identify jets of the same wavefunction. The real-to-complex embedding is isometric: the only additional factor is `|Γ|`.

## Pointwise assembly and L² passage

Leibniz gives a finite sum of the preceding jets. With the semiclassical factor `hⁿ`, the remaining power is exactly `hⁿ h⁻⁽ⁿ⁺²⁾=h⁻²`. On each closed cusp support, geometry and `κ≤1/16` give

\[
 \kappa T(x)-[J(E,\|x\|)-J(E,R)]\le-t/16.
\]

[`LogFlatWeightedAction`](../InfiniteZero/LogFlatWeightedAction.lean) combines this inequality with the margin `β₂−β₁` to give the global cost `exp(−β₁log²(1/h))`, including at `t=0`. [`CuspFineForcingJets`](../InfiniteZero/CuspFineForcingJets.lean) proves the assembly

\[
 e^{\kappa T(x)/h}h^n\|D^n(W\phi)(x)\|
 \le C_n\Gamma h^{-2}e^{-J_b(E,R)/h}
                       e^{-\beta_1\log^2(1/h)}.
\]

For directions of norm at most one, jet evaluation is bounded by the operator norm. Its support remains in a fixed ball, so the pointwise bound gives the same L² bound up to a fixed area factor. [`AtomicCuspFineForcingDerivatives`](../InfiniteZero/AtomicCuspFineForcingDerivatives.lean) defines this actual wavefunction as `weightedAtomicForcingJet`. Its continuity, support, and L² membership are proved, and its mass is bounded by the **full square** of the displayed envelope. This retains a single factor `Γ` and the full coefficient `β₁` in norm.

## Same actual state, same coefficient, all required orders

[`RadialCoreFineForcingDerivatives`](../InfiniteZero/RadialCoreFineForcingDerivatives.lean) chooses a threshold and constant common to orders `j≤n`, then passes to `λ=h⁻¹`. It uses the effective core energy in `[1/2,1]` and the already-proved exterior representation. For **every** actual positive radial core ground state, a single `Γ>0` gives its tail and the estimates of all jets considered. This universal version allows reuse of exactly the reference employed by the Schur certificate and full-potential comparison.

The order of choices is `n,β₁,χ`, then `C,N`, then `λ≥N` and the state, then `Γ`, then `κ,j≤n` and the directions. No constant depends on separation `L`. A second version also chooses an actual positive radial state, whose existence comes from the core data.

The public wrapper [`radialCore_fine_forcing_derivatives`](../InfiniteZero/ClassicalCuspForcingDerivatives.lean) requires only `BasicConditions`, `0<β₁<β`, and maximum order `n`. It chooses the weight before coupling and supplies both classical inputs A002 and A004. No tail, spectral-bound, or small-source assumption is added.

For sums of norms, [`GenericFiniteL2Bound`](../InfiniteZero/GenericFiniteL2Bound.lean) identifies mass with the squared norm of the actual `toLp` vector. The sum of a finite family of jets bounded by the same envelope is therefore at most its cardinality times that envelope; the cardinality is fixed for a fixed maximum order. The corollary `exists_radialCore_fine_forcing_derivatives_sum_of_radialData` encodes this sum for every finite family of jets of orders at most `n`, without changing the state, energy, or Γ.

## Preparing interior propagation

[`LipschitzExponentialWeightLocal`](../InfiniteZero/LipschitzExponentialWeightLocal.lean) also proves local weight comparison on `dist(x,x₀)≤ρh`:

\[
 e^{-\kappa K\rho}\le
 \frac{e^{\kappa T(x)/h}}{e^{\kappa T(x_0)/h}}
 \le e^{\kappa K\rho}.
\]

For the actual cusp weight, a common constant is chosen before `h`, the centers, and `κ` in a fixed interval. This weight comparison is an input to the [elliptic estimate](ATOMIC_RESPONSE_JETS.md). The exact PDE multiplied by `h²`, rescaling on an h-scale ball, and application of the interior contract A005 are now assembled; they do not follow from weight comparison alone.

## Full right-hand side now controlled

The [proof of sharp data](ATOMIC_FINE_RESPONSE_DATA.md) now assembles both terms of the actual right-hand side `f=−cWφ+cδφ`, where `δ=h²(Efull−Ecore)`. Scalar control gives `|δ|≤3‖exp(κT/h)Wφ‖₂`, with a single Γ factor. The [normalized radial jets](RADIAL_WEIGHTED_JETS.md) are bounded without Γ on a fixed annulus containing the cusps: unit mass, radial monotonicity, and the kernel lower bound control the same exterior normalization, which the action margin then absorbs. The second term of f therefore produces no Γ².

`AtomicFineResponseData` obtains, for all `j≤n`, a pointwise bound on `exp(κT/h)hʲ‖Dʲf‖` by `CcΓh⁻² exp(−J/h)exp(−β₁log²(1/h))` on this annulus. `AtomicFineResponseDecomposition` retains the same actual states, c, Γ, PDE, and global L² bound on η with prefactor `cΓh⁻³`. It also supplies local masses and finite sums of actual L² norms of f’s jets on `cuspPacketNeighborhood`. The weight and indicator are applied after differentiation.

The constants and threshold precede coupling; the states, c, and Γ precede κ, the order, and directions. The finite family comes next, with explicit cardinality. This completes the data content of `sublemma:T3-4-forcing-derivatives` without a new analytic admission.

## Scope

This variant uses a less precise polynomial prefactor than the TeX, but retains the entire action and every coefficient `β₁<β`. The polynomial power is unspecified in `sublemma:T3-4-weighted-forcing`. Exact chart-integration formulas and the manuscript’s optimal prefactors are unnecessary for this route.

The full PDE data are then used in [elliptic propagation](ATOMIC_RESPONSE_JETS.md), which supplies pointwise correction jets through A005. The [full scattered-source profile](CUSP_SCATTERED_SOURCE.md), with local log-flat factor, is then assembled for the same states. The [cell estimates and hopping](ACTIVE_CHANNEL_ASYMPTOTIC.md) are also proved and used in [thm_main](../InfiniteZero/Remaining.lean), modulo A002–A005. The incoming source’s local profile and the TeX’s optimal prefactor `h⁻⁷/²` are not claimed by this global bound.
