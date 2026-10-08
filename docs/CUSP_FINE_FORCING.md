# Cusp forcing: exact action and log-flat bound

This page explains the `k=0` case of `sublemma:T3-4-weighted-forcing` and its application to `sublemma:T3-4-weighted-response`. The [extension to forcing derivatives](CUSP_FORCING_DERIVATIVES.md) is now proved. [Propagation to correction jets](ATOMIC_RESPONSE_JETS.md) is established in a separate block using the proved interior estimate. No source or tunneling estimate is admitted to obtain the bounds below.

The global build, `assert_no_sorry` guards, dependency export, and blueprint index were checked by `scripts/check.sh`. The new analytic theorems use only standard Lean axioms; this block’s public wrapper uses exactly A002 and A004. The [final proof of thm_main](../InfiniteZero/Remaining.lean) is now compiled modulo the two classical admissions A002 and A004.

## Actual parameters, energy, and state

Fix `p.BasicConditions`, the weight `T=χ.weight`, and `0<β₁<p.β`. Write `h=λ⁻¹`, `W=p.potential−p.core`, and `Ecore,h=−λ⁻² atomicGroundEnergy p.b p.core λ`. The weight equals the positive normal coordinate on both cusps.

[`RadialCoreEnergyBounds`](../InfiniteZero/RadialCoreEnergyBounds.lean) proves `Ecore,h∈[1/2,1]` beyond a threshold fixed before `λ`. The physical-energy lower bound `−λ²` uses `core≥−1`, the closed operator domain, and its actual normalized eigenstate; its upper bound `−λ²+Bλ` comes from radial spectral data. No full-potential spectral information is used here.

The exterior representation already established for every actual positive radial ground state is `φcore(x)=Γ K(b,h,Ecore,h,‖x‖)` for `‖x‖>r₀`, with `Γ>0`. The coefficient of **this same state** is retained throughout the estimates; it is not replaced by a constant independent of `h`.

## Pointwise bound without action loss

[`LandauKernelExactActionUpper`](../InfiniteZero/LandauKernelExactActionUpper.lean) chooses the kernel splitting parameter equal to `h`. The already-proved bound

\[
 K(b,h,E,r)\le\frac{1}{\pi E r^2\alpha^2}
                  e^{-(1-\alpha)J_b(E,r)/h}
\]

gives, for `α=h≤1`,

\[
 K(b,h,E,r)\le \frac{e^{J_b(E,r)}}{\pi E r^2}
                   h^{-2}e^{-J_b(E,r)/h}.
\]

The prefactor is uniformly bounded on the fixed real rectangle `E∈[1/2,1]`, `r∈[R,cuspSupportRadius]`. This bound uses `h⁻²` rather than the manuscript’s optimal prefactor `h⁻³/²`, which suffices here because the polynomial power `M` is unspecified. The exponential action remains exact.

[`CuspWeightedActionGain`](../InfiniteZero/CuspWeightedActionGain.lean) combines the specific support geometry, `r≥R+t/4`, with `∂r J≥√E≥1/2`. It deduces `J(E,r)−J(E,R)≥t/8`. For `0≤κ≤1/16`, the weight therefore leaves a gain `t/16`:

\[
 \kappa T(x)-\bigl(J(E,\|x\|)-J(E,R)\bigr)\le-t/16.
\]

The cutoff bound gives `|q±|≤a exp(−β log²(t*/t))` on each open support, where `t>0`. The pointwise lemma `eventually_logFlat_laplace_le`, applied with `aMin=1/16` and `η=β−β₁`, gives uniformly in `t>0`

\[
 e^{-\beta\log^2(t_*/t)-t/(16h)}
 \le e^{-\beta_1\log^2(1/h)}.
\]

Adding both cusps and retaining `ε`, [`CuspFineForcingPointwise`](../InfiniteZero/CuspFineForcingPointwise.lean) obtains a constant fixed before `h,E,κ,Γ,φ` such that

\[
 |e^{\kappa T(x)/h}W(x)\phi(x)|
 \le C\Gamma h^{-2}e^{-J_b(E,R)/h}
                  e^{-\beta_1\log^2(1/h)}.
\]

This step requires only the exterior representation of `φ`; it assumes no estimate on `Wφ` or the scattered response.

## Passage to the physical norm

The source is supported in a fixed ball of radius `cuspSupportRadius`. [`GenericCompactL2Bound`](../InfiniteZero/GenericCompactL2Bound.lean) proves that a pointwise bound `B` on such a source gives norm `≤√π·cuspSupportRadius·B` in the actual `L²` space. [`AtomicCuspFineForcing`](../InfiniteZero/AtomicCuspFineForcing.lean) identifies representatives of both multipliers and applies this bound, yielding

\[
 \|e^{\kappa T/h}W\phi_{\rm core}\|_2
 \le C\Gamma h^{-2}e^{-J_b(E_{\rm core,h},R)/h}
                     e^{-\beta_1\log^2(1/h)}.
\]

This route avoids integration in cusp charts for `k=0`. It retains the full coefficient `β₁`, because pointwise estimation precedes squaring and integration. The `λ²` factor of the unscaled source is separate: the residual `λ²Wφcore` costs `h⁻⁴`.

## Application to the same correction

`exists_atomicGround_weighted_decay_and_response_of_radialData` simultaneously retains the coefficient `c∈[1/2,1]` and the exact forced bound for a single Schur certificate `q`. With `η=ψfull−cφcore`, this is

\[
 \|e^{\kappa T/h}\eta\|_2
 \le \frac{12c}{\gamma h}\|e^{\kappa T/h}W\phi_{\rm core}\|_2.
\]

[`AtomicGroundFineResponse`](../InfiniteZero/AtomicGroundFineResponse.lean) uses the energy and tail of the same `s.coreState`, fixes `κ₀≤min(κresolvent,1/16)`, and enlarges the common threshold. This gives

\[
 \|e^{\kappa T/h}\eta\|_2
 \le Cc\Gamma h^{-3}e^{-J_b(E_{\rm core,h},R)/h}
                      e^{-\beta_1\log^2(1/h)}.
\]

The weight, `κ₀,C`, and threshold are chosen before `λ`; the states, `c`, and `Γ` precede `κ`. No constant depends on the separation `L`, which does not occur in this atomic block. The actual application’s only classical inputs are A002 and A004, without A003.

[`AtomicGroundFineDecomposition`](../InfiniteZero/AtomicGroundFineDecomposition.lean) recovers smooth representatives of these same vectors. The statement retains the actual tail of `φcore`, `c∈[1/2,1]`, orthogonality of `η`, weighted mass bounded by the square of the right-hand side above, and the exact PDE at every point. The wrapper [`atomicGround_fine_weighted_decomposition`](../InfiniteZero/Remaining.lean#L286) requires only `BasicConditions` and `0<β₁<β`. It chooses the cutoffs before the coupling; its only admissions are the classical inputs A002 and A004.

## Energy shift: a single forcing factor

[`AtomicEnergyShiftForcing`](../InfiniteZero/AtomicEnergyShiftForcing.lean) starts from the scalar equation of the same Schur certificate. The diagonal shift and off-diagonal coupling are each bounded by `‖λ²Wu‖`, hence

\[
 |E_{\rm full}-E_{\rm core}|
 \le(1+\|\zeta\|_2)\|\lambda^2Wu\|_2.
\]

The normalization `c=(1+‖ζ‖²)⁻¹/²≥1/2` implies `‖ζ‖²≤3`, hence `1+‖ζ‖≤3`. Multiplying by `λ⁻²`, then using `T≥0` and `κ≥0`,

\[
 |\lambda^{-2}(E_{\rm full}-E_{\rm core})|
 \le3\|Wu\|_2\le3\|e^{\kappa\lambda T}Wu\|_2.
\]

This realizes `sublemma:T3-4-energy-forcing` without having to absorb a squared forcing term. Thus `Γ` appears only once when the sharp bound is inserted. No additional small-forcing assumption is needed beyond the normalization threshold already constructed.

## Scope and connections

The forcing derivatives `k>0` are now treated in the [dedicated block](CUSP_FORCING_DERIVATIVES.md), then assembled with the energy-shift term in the [full PDE data](ATOMIC_FINE_RESPONSE_DATA.md). The [elliptic step](ATOMIC_RESPONSE_JETS.md) then supplies pointwise correction jets using the proved interior estimate. The [full scattered-source profile](CUSP_SCATTERED_SOURCE.md) now retains both log-flat factors. [L¹ integration of the profiles](CUSP_SOURCE_L1.md) is also proved; the [full active-cell integral](INCOMING_PHYSICAL_ASYMPTOTIC.md) and its [connection to the channels](ACTIVE_CHANNEL_ASYMPTOTIC.md) are established in separate modules.
