# Weighted response of the actual atomic ground state

The Schur components, response equation, weighted residual, and assembly retaining the positive radial choice compile without warnings. The global check passed: the build, public wrapper, `Verification`, and axiom-dependency export are validated. This block adds no admission: its inputs are radial data and both explicit operator realizations, obtained from A004 and A002 through the proved radial assembly when specialized to the constructed potential.

## Statement and common choices

Fix `p.BasicConditions` and cutoffs `χ : CuspWeightCutoffs p`. Write `W=p.potential−p.core=ε(q₊+q₋)`, `T=χ.weight`, and `Mκ=exp(κλT)`, an actual bounded multiplier on physical `L²`. The weight is fixed before `λ`, nonnegative, zero near the core, and equal to the normal coordinate on the cusp supports.

[`RadialCoreGroundChoice`](../InfiniteZero/RadialCoreGroundChoice.lean) proves that the positive radial choice in `RadialCoreSpectralData` also carries the contract’s test-function gap. The gap extends to the closed core graph, forces simplicity of its ground eigenspace, and shows that the two witnesses differ by a unit phase. The overlap norm is invariant under this phase: no gap constant is lost and no classical field is added.

`exists_atomic_cusp_weighted_reference_of_radialData` then retains a single reference `s : AtomicSchurReference`, with `IsPositiveRadial s.coreState`, and its compressed resolvents for all energies `E≤Ecore`. The reference precedes `E` and `κ`, and each resolvent precedes `κ`.

[`AtomicGroundWeightedResponse`](../InfiniteZero/AtomicGroundWeightedResponse.lean) applies this construction to `Efull≤Ecore`. It chooses a quantitative certificate `q` of the actual full ground state from the same reference `u=s.vector`. If `ζ=q.correction`, the vectors and coefficient are

\[
c=(1+\|\zeta\|_2^2)^{-1/2},\qquad
v=c(u-\zeta),\qquad \eta=v-cu=-c\zeta.
\]

`u` and `v` are normalized; `u` represents the positive radial ground state, `v` belongs to the eigenspace at `Efull`, and `η` belongs to the actual full operator domain. The correction is orthogonal to `u`. These choices precede `κ`. Their phases need not be identified with those of `canonicalAtomicState`.

## Exact equation and bound by actual forcing

Domain equality under bounded perturbation gives `A u=Ecore u+λ²Wu`, where `A` is the unscaled full operator. [`SchurResponseEquation`](../InfiniteZero/SchurResponseEquation.lean) proves in this same domain

\[
(A-E_{\rm full})\eta
 =-c\lambda^2 Wu+c(E_{\rm full}-E_{\rm core})u.
\]

Both signs and the coefficient `c` are retained. This equality is also recorded as a point of the graph of `A`.

[`WeightedSchurCorrection`](../InfiniteZero/WeightedSchurCorrection.lean) identifies `ζ` with the resolvent applied to the projected residual. The projection remains inside `Mκ ι(A_Q−Efull)⁻¹ Q Mκ⁻¹`: it is not assumed to commute with the weight. The already-proved bound `12/(γλ)` on this operator gives

\[
\boxed{\ \|M_\kappa\eta\|_2
 \le \frac{12c\lambda}{\gamma}\,\|M_\kappa Wu\|_2\ }.
\]

This is exactly the conclusion of `exists_atomicGround_weighted_response_of_radialData`. The right-hand side is the actual perturbation applied to the same core ground state. It already includes `ε`; no sharp estimate of this forcing is assumed. In semiclassical variables, the coefficient is `12c/(γh)` and the preceding equation is divided by `λ²`, with `h=λ⁻¹`.

## Initial absolute decay and normalization

[`AtomicWeightedResidual`](../InfiniteZero/AtomicWeightedResidual.lean) starts from the core’s Agmon tail and the established bound `‖λ²Wu‖₂≤Kλ exp(−d₀λ)`. If `0≤T≤M`, the multiplier costs at most `exp(κλM)`. The fixed choice `κ₀=d₀/(2(M+1))` retains at least half the exponential rate, uniformly over every normalized core ground state:

\[
\|M_\kappa\lambda^2 Wu\|_2\le K\lambda e^{-d_0\lambda/2}.
\]

[`AtomicGroundWeightedDecay`](../InfiniteZero/AtomicGroundWeightedDecay.lean) deduces the existence of `κ₀,C,d,N>0`, fixed before coupling, such that for every `λ≥N` the same `s,q` satisfy

\[
\tfrac12\le c\le1,\qquad
\forall\kappa\in[0,\kappa_0],\quad
\|M_\kappa\eta\|_2\le C e^{-d\lambda}.
\]

The theorem is `exists_atomicGround_weighted_decay_of_radialData`. The reference, actual ground vector, and `c` are chosen before `κ`. The constants do not depend on separation `L`, which is absent from the statement. From the bound on `ζ`, `SchurNormalizationThreshold` separately proves `0≤1−c≤K₁² exp(−2d₁λ)` with the threshold preceding the vector; the assembly above explicitly retains `c∈[1/2,1]`.

## Decomposition of actual wavefunctions

[`AtomicResponseWavefunction`](../InfiniteZero/AtomicResponseWavefunction.lean) chooses the smooth representative `ψ` of the exact normalized vector of `q`, through `s.exists_responseWavefunction q hApot`. Then `η(x)=ψ(x)−cφcore(x)` is smooth and `L²`, represents exactly `q.normalizedCorrection`, and satisfies the differential equation above at every point of the plane. The proof uses both actual eigenvalue equations and Hamiltonian linearity; it uses no additional pointwise elliptic estimate.

[`WeightedWavefunctionL2`](../InfiniteZero/WeightedWavefunctionL2.lean) identifies the L² multiplier norm with the weighted function’s mass. The compiled assembly [`AtomicGroundWeightedDecomposition`](../InfiniteZero/AtomicGroundWeightedDecomposition.lean), `exists_atomicGround_weighted_decomposition_of_radialData`, thus supplies two actual normalized ground wavefunctions `φcore,ψfull`, with `φcore` positive radial, and a common `c∈[1/2,1]`, such that

\[
\langle\phi_{\rm core},\eta\rangle=0,\qquad
\int e^{2\kappa\lambda T(x)}|\eta(x)|^2\,dx
 \le C^2e^{-2d\lambda},\qquad \eta=\psi_{\rm full}-c\phi_{\rm core}.
\]

The pointwise PDE belongs to the same conclusion; both states and `c` precede the quantifier `∀κ∈[0,κ₀]`. The integrals are actual Lebesgue integrals and their finiteness follows from the bounded weight action. The compiled wrapper `CuspParameters.atomicGround_weighted_decomposition`, in `Remaining`, also chooses the cutoffs before `λ` and requires only `BasicConditions`, using A002+A004. It does not use A003.

## Sharp estimates and scope

The [sharp forcing block](CUSP_FINE_FORCING.md) now applies the tail `φcore=ΓK` to the norm of `Wu`. The bound is `CΓh⁻² exp(−J(Ecore,h,R)/h−β₁log²(1/h))`, for every `0<β₁<β`. `AtomicGroundFineResponse` retains the same normalized certificate and deduces `CcΓh⁻³ exp(−J(Ecore,h,R)/h−β₁log²(1/h))` for the weighted correction. `AtomicGroundWeightedDecay` also exports a version simultaneously retaining `c∈[1/2,1]`, absolute decay, and the exact forced bound.

The [forcing derivatives](CUSP_FORCING_DERIVATIVES.md), then those of the [full right-hand side](ATOMIC_FINE_RESPONSE_DATA.md), are now controlled with the same global bound. The local PDE data retain a single factor `cΓ` and the same wavefunctions. The [elliptic step](ATOMIC_RESPONSE_JETS.md) then supplies pointwise jets of the same correction using the proved interior estimate. Multiplication by λ²W now gives the [full scattered-source profiles](CUSP_SCATTERED_SOURCE.md), retaining both log-flat factors separately. The [full active cell](ACTIVE_CHANNEL_ASYMPTOTIC.md) and [relative spectral errors](../InfiniteZero/CanonicalParityRelativeErrors.lean) are also proved in separate blocks. Their [final assembly](../InfiniteZero/Remaining.lean) concludes `thm_main`, modulo the two classical admissions A002 and A004.
