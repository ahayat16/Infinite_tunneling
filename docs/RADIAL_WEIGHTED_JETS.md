# Weighted jets of the actual radial state, without a tail coefficient

The modules [RadialCorePointwiseBound](../InfiniteZero/RadialCorePointwiseBound.lean), [RadialCoreNormalizationUpper](../InfiniteZero/RadialCoreNormalizationUpper.lean), and [RadialCoreWeightedJetBounds](../InfiniteZero/RadialCoreWeightedJetBounds.lean) compile without warnings. Their theorem audit finds only `propext`, `Classical.choice`, and `Quot.sound`. The global check `scripts/check.sh` passed: compilation, guards, and dependency export.

No admission is added. Statements at the effective energy explicitly take `hRad : RadialCoreSpectralData p.b p` and core realizations `hAcore : ∀ λ, IsMagneticRealization p.b λ p.core`. The radial data are assembled from A002+A004, and A002 supplies the realizations in the wrapper `atomicGround_fine_response_data`, whose connection to the PDE is described in [ATOMIC_FINE_RESPONSE_DATA.md](ATOMIC_FINE_RESPONSE_DATA.md). A003 is not used.

## Conventions and retained choices

Fix `hp : p.BasicConditions`, cutoffs `χ : CuspWeightCutoffs p`, real weight `T=χ.weight`, a finite outer radius `rMax≥R/2`, and maximum order `n`. Write

\[
h=\lambda^{-1},\qquad
E_h=-h^2 E_{\rm core}(\lambda),\qquad
J(E,r)=\operatorname{bridgeAction}(b,E,r).
\]

For every sufficiently large coupling, the already-proved bound on the actual core energy gives `E_h∈[1/2,1]`. The state `φ` satisfies the actual predicate `IsAtomicGroundState b p.core λ φ`, hence is a smooth L² eigenfunction of mass exactly one. Also assume `IsPositiveRadial φ`: its profile `f(r)=realRadialProfile φ r` is real and strictly positive, and `φ(x)=f(‖x‖)`.

The exterior representation, obtained through the ODE and Wronskian, belongs to the **same state**:

\[
\phi(x)=\Gamma K_{b,h,E_h}(\|x\|),\qquad \|x\|>r_0,
\qquad \Gamma>0.
\]

The upper bound on `Γ` below applies to any supplied coefficient satisfying this equality; it does not choose another tail or phase. The positive radial choice is not identified with the arbitrary phase of `canonicalAtomicState`.

## Normalized mass controls an exterior value

`IsAtomicGroundState.core_profile_le_inv_sqrt_pi_mul_radius` proves, for every `r>0`,

\[
f(r)\le\frac{1}{\sqrt\pi\,r}.
\]

Decrease of the profile follows from its concrete ODE through `IsAtomicGroundState.core_profile_antitone`. For `‖x‖<r`, therefore, `|φ(x)|²≥f(r)²`. Integration over the disk, whose actual area is exactly `πr²`, gives

\[
\pi r^2 f(r)^2
\le\int_{\|x\|<r}|\phi(x)|^2\,dx
\le\int_{\mathbb R^2}|\phi(x)|^2\,dx=1.
\]

Positivity of `f(r)` allows taking the square root. Integrability comes from `MemLp φ 2 volume`, supplied by the actual eigenstate. This step uses neither harmonic approximation nor an admitted pointwise estimate.

## Upper bound on the same exterior normalization

Fix the reference radius `rref=2r₀`, strictly outside the core. For every fixed action loss `η_act>0`, the uniform lower bound already proved in [LandauKernelUniform](../InfiniteZero/LandauKernelUniform.lean) gives a constant `cη>0` such that

\[
K_{b,h,E}(2r_0)
\ge c_\eta h^{-2}
  \exp\!\left(-\frac{J(E,2r_0)+\eta_{\rm act}}h\right),
\qquad E\in[1/2,1],\ h>0.
\]

On the other hand, the value of the same tail at this radius satisfies

\[
\Gamma K_{b,h,E}(2r_0)=f(2r_0)
\le\frac{1}{2\sqrt\pi\,r_0}.
\]

The kernel lower bound is strictly positive. Division gives

\[
\boxed{\quad
\Gamma\le C_\eta h^2
  \exp\!\left(\frac{J(E,2r_0)+\eta_{\rm act}}h\right).
\quad}
\]

`exists_radialCore_coefficient_exp_upper` first treats every positive scale and every energy in this interval, under the supplied tail equality. `exists_radialCore_coefficient_exp_upper_of_radialData` then applies the result at `h=λ⁻¹` and the effective core energy. Its constants and threshold precede `λ`, `φ`, and `Γ`. The loss `η_act` is also fixed before them. This is an exponential upper bound with arbitrary positive loss, not a normalization asymptotic or harmonic profile.

## Eliminating Γ in every weighted jet

Set

\[
r_{\min}=R/2,\qquad
\Delta=\frac{R/2-2r_0}{2}>0.
\]

Positivity follows from `8r₀<R`. The radial action derivative satisfies `∂rJ≥√E≥1/2` for `E∈[1/2,1]`. Thus, for `r≥R/2`,

\[
J(E,r)-J(E,2r_0)\ge\Delta.
\]

This is `radialCore_annulus_action_gap`. The weight is continuous and compactly supported, so `0≤T≤M` for a fixed constant `M>0`. The proof chooses

\[
\eta_{\rm act}=\Delta/4,\qquad
\kappa_0=\min\!\left(\frac1{16},\frac\Delta{4(M+1)}\right)>0.
\]

For `κ∈[0,κ₀]`, the weight cost satisfies `κT(x)≤Δ/4`, independently of `λ`. The [exterior jet bounds](../InfiniteZero/ExteriorRadialJetBounds.lean) simultaneously give, for every `j≤n` on the fixed annulus,

\[
\|D^j\phi(x)\|
\le C_n\Gamma h^{-(n+2)}e^{-J(E_h,\|x\|)/h}.
\]

Here `D^j=iteratedFDeriv ℝ j`, and the norm is the real multilinear operator norm with complex values. The tail identity determines these jets through local equality of functions; the coefficient does not change with `j`.

The preceding upper bound on `Γ` cancels the factor `h⁻²` exactly. For `0<h≤1`, bounding `h^j` by one gives

\[
e^{\kappa T(x)/h}h^j\|D^j\phi(x)\|
\le C h^{-n}e^{-\Delta/(2h)}.
\]

The scalar lemma `weighted_jet_le_of_tail_bounds` retains this cancellation and all three exponent contributions. Finally, for fixed `n`, `λⁿ≤exp((Δ/4)λ)` beyond a threshold. This yields

\[
\boxed{\quad
e^{\kappa\lambda T(x)}\lambda^{-j}\|D^j\phi(x)\|
\le C e^{-d\lambda},\qquad
d=\frac\Delta4=\frac{R/2-2r_0}{8}>0.
\quad}
\]

The API is `exists_radialCore_weighted_jet_decay_of_radialData`: `∃κ₀>0`, with `κ₀≤1/16`, then `∃C,d,N>0`, then **every** `λ≥N`, every actual positive radial ground state, every `κ∈[0,κ₀]`, every `x` in the closed annulus `[R/2,rMax]`, and every `j≤n`. The conclusion no longer contains `Γ`. The threshold is common to all orders and states. The weight multiplies after differentiation; no derivative of the Lipschitz weight occurs. This fixed-annulus bound is not a global bound on the whole plane.

## Use for the second energy term

The semiclassical response equation’s source has the exact form

\[
F_h=-cW\phi+c\,h^2(E_{\rm full}-E_{\rm core})\phi,
\qquad W=p.\mathrm{atomicPerturbation}.
\]

Scalar Schur control retains the same reference and certificate. Under the already-constructed normalization `c≥1/2`, [AtomicEnergyShiftForcing](../InfiniteZero/AtomicEnergyShiftForcing.lean) gives

\[
|h^2(E_{\rm full}-E_{\rm core})|\le3\|W\phi\|_2.
\]

The sharp forcing on the right has a single Γ factor. To bound jets of the second term of `F_h`, the present estimate controls its radial factor `φ` by `Ce^{-d/h}`, without reintroducing Γ. The product therefore retains one normalization factor; leaving radial jets as Γ times kernel jets would artificially produce Γ². This closes precisely the radial factor needed for this step. The response equation and both terms still belong to the same states and coefficient `c`.

## Local preparation and limits of this step

[CuspPacketNeighborhood](../InfiniteZero/CuspPacketNeighborhood.lean) constructs two fixed open annuli. The closed supports of both cusps and `W` lie in the inner annulus; its closure is compact and contained in the outer annulus. With `rMax=cuspPacketRadius`, the latter lies in the closed annulus of the bound above. An explicit positive scale ensures that every closed ball of radius `2h` centered in the inner closure remains in the outer neighborhood.

[LipschitzExponentialWeightLocal](../InfiniteZero/LipschitzExponentialWeightLocal.lean) supplies local weight comparison. If `T` is `K`-Lipschitz and `dist(x,x₀)≤ρh`, then

\[
e^{-\kappa K\rho}\le
\frac{e^{\kappa T(x)/h}}{e^{\kappa T(x_0)/h}}
\le e^{\kappa K\rho}.
\]

For `κ` in a fixed interval, these constants are independent of `h` and the center. This preparation transports estimates on semiclassical balls without differentiating the weight.

These results control the radial factor of the second energy term; they are an input to the elliptic estimate for `η_corr=ψfull−cφ`. The [full right-hand side](ATOMIC_FINE_RESPONSE_DATA.md), then [passage to pointwise jets](ATOMIC_RESPONSE_JETS.md) using the proved interior estimate, are proved separately. The [source profiles](CUSP_SOURCE_PROFILES.md), [active channels](ACTIVE_CHANNEL_ASYMPTOTIC.md), and [final assembly](../InfiniteZero/ConstructedMainProof.lean) are also established. [thm_main](../InfiniteZero/Remaining.lean) is compiled modulo the two classical admissions A002 and A004.
