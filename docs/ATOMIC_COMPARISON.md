# Exponential comparison with the radial-core ground state

The connection from Agmon decay to the **actual atomic residual** is proved in [AtomicResidualDecay.lean](../InfiniteZero/AtomicResidualDecay.lean), without further admissions. The quantitative Schur certificate and its assembly in [AtomicGroundComparison.lean](../InfiniteZero/AtomicGroundComparison.lean) now compile without warnings: the core and full-potential ground energies are exponentially close, as are normalized ground vectors whose relative phase is fixed by strictly positive real overlap.

## Data and conventions

Fix `p : CuspParameters`, `hp : p.BasicConditions`, data `hRad : RadialCoreSpectralData p.b p`, and explicit realizations of the core and full potential at every coupling. Write

\[
 A_\lambda=H_\lambda(p.\mathrm{potential}),\qquad
 A^0_\lambda=H_\lambda(p.\mathrm{core}),\qquad
 W=\varepsilon(q_++q_-),\qquad
 E^0_\lambda=\operatorname{atomicGroundEnergy}(p.b,p.\mathrm{core},\lambda).
\]

These are **unscaled** energies: the potential term is `λ²V` and the complement gap will be `g₀λ`, with `g₀ = hRad.gap / 2 > 0`. The multiplier `atomicPerturbationMul hp` represents only `W`. The residual to estimate is therefore `λ² atomicPerturbationMul hp u`, not this multiplier alone.

These modules retain the radial and realization inputs as arguments. Applying them from `BasicConditions` alone uses the classical admissions A004 and A002, documented separately in [RADIAL_HARMONIC_CONTRACT.md](RADIAL_HARMONIC_CONTRACT.md) and [CLASSICAL_OPERATOR_REALIZATION.md](CLASSICAL_OPERATOR_REALIZATION.md). No nonradial comparison, decay, or Schur result is added to those admissions. A003, concerning the free resolvent kernel, is not used in this proof.

## 1. From cusp support to exponential residual

At every point of the plane,

\[
 |W(x)|\le2\varepsilon a,\qquad
 W(x)=0\quad\text{if }\|x\|\le4r_0.
\]

The second property follows from cusp support in `‖x‖ ≥ R/2` and `8r₀ < R`. Both properties are proved in [AtomicPerturbationTail.lean](../InfiniteZero/AtomicPerturbationTail.lean). For every `u : L2Space` represented by `φ`, it gives

\[
 \|\lambda^2 W u\|_2^2
 \le(2\lambda^2\varepsilon a)^2
       \int_{\|x\|\ge4r_0}|\phi(x)|^2\,dx.
\]

`Represents u φ` is almost-everywhere equality with the representative of the L² class; it implies `MemLp φ 2 volume`. Integrability and passage from the L² multiplier to the pointwise product are proved. No additional regularity of the representative is required for the multiplier inequality alone.

[AtomicGroundAgmon.lean](../InfiniteZero/AtomicGroundAgmon.lean) supplies `C,d,T > 0`, chosen before `λ` and the state, such that every normalized core ground state satisfies, for `λ ≥ T`,

\[
 \int_{\|x\|\ge4r_0}|\phi_{0,\lambda}(x)|^2\,dx
 \le\frac C{\lambda^2}e^{-2d\lambda}.
\]

The energy hypothesis needed for Agmon is deduced from radial data, and the [global Agmon proof](AGMON_DECAY.md) actually removes cutoffs at infinity. Combining the two inequalities gives

\[
 r_\lambda:=\|\lambda^2Wu_{0,\lambda}\|_2
 \le K\lambda e^{-d\lambda},\qquad K=2\varepsilon a\sqrt C>0.
\]

This is exactly `CuspParameters.exists_atomicResidual_decay_of_radialData`. The constants are chosen before the coupling, **all** core ground states, and **all** their L² representatives. The squared version is `exists_atomicResidual_sq_decay_of_radialData`. Both conclusions and the conversion lemma `norm_scaled_atomicPerturbationMul_le_of_exterior_mass` compile without warnings, and their audit finds only `propext`, `Classical.choice`, and `Quot.sound`.

## 2. From the residual to the energy shift

Domain transfer under bounded perturbation gives the exact graph point

\[
 A_\lambda u_{0,\lambda}=E^0_\lambda u_{0,\lambda}
                          +\lambda^2Wu_{0,\lambda}.
\]

The normalized radial vector therefore belongs to the actual full domain. Set `P = |u₀⟩⟨u₀|`, `Q = 1−P`, `aλ = Re⟨u₀,Aλu₀⟩`, and `Bλ = QAλu₀`. Projection contraction and Cauchy–Schwarz give

\[
 \|B_\lambda\|\le r_\lambda,\qquad
 |a_\lambda-E^0_\lambda|\le r_\lambda,\qquad
 a_\lambda\le E^0_\lambda.
\]

The first two bounds are in [SchurResidualBounds.lean](../InfiniteZero/SchurResidualBounds.lean); the last uses the already-proved nonpositivity of the real multiplier `W`. [AtomicSchurReference.lean](../InfiniteZero/AtomicSchurReference.lean) constructs these data from an actual radial ground state and retains actual complement coercivity, with `gλ = g₀λ`.

The Schur complement constructs a root `Eλ ≤ E⁰λ` and a correction `ζλ ∈ QL²` in the compressed operator’s domain, such that

\[
 (QA_\lambda Q-E_\lambda)\zeta_\lambda=B_\lambda,
 \qquad
 a_\lambda-E_\lambda=\operatorname{Re}\langle B_\lambda,\zeta_\lambda\rangle.
\]

The results `schur_correction_norm_le` and `schur_energy_shift_bounds` in [SchurGroundEstimates.lean](../InfiniteZero/SchurGroundEstimates.lean) prove

\[
 \|\zeta_\lambda\|\le\frac{\|B_\lambda\|}{g_\lambda},\qquad
 0\le a_\lambda-E_\lambda\le\frac{\|B_\lambda\|^2}{g_\lambda}.
\]

The quantitative connection retains **the same root and vector** in a `GroundStateCertificate`, so that operator realization identifies its energy with the full ground energy. This leads to

\[
 0\le\delta_\lambda:=E^0_\lambda-E_\lambda
 \le r_\lambda+\frac{r_\lambda^2}{g_\lambda}
 \le\left(K+\frac{K^2}{g_0}\right)\lambda e^{-d\lambda}.
\]

The last absorption is proved in [SchurExponentialBounds.lean](../InfiniteZero/SchurExponentialBounds.lean). The same module gives `λ exp(−dλ) ≤ (2/d) exp(−(d/2)λ)`. The final connection uses the explicit constants `C_E = (K + K²/g₀) (2/d)` and `d_E = d/2` for `0 ≤ δλ ≤ C_E exp(−d_E λ)`.

[SchurGroundQuantitative.lean](../InfiniteZero/SchurGroundQuantitative.lean) and [AtomicGroundComparison.lean](../InfiniteZero/AtomicGroundComparison.lean) prove this assembly. The final theorem `exists_atomicGroundEnergy_exponential_comparison_of_radialData` gives `∃ C_E > 0, ∃ d_E > 0, ∃ T > 0`, then, for every `λ ≥ T`, the displayed comparison of the two actual `atomicGroundEnergy` values.

## 3. Normalization and positive phase

The reconstructed vector is `wλ = u₀,λ − ζλ`. Orthogonality gives exactly

\[
 \|w_\lambda\|^2=1+\|\zeta_\lambda\|^2,\qquad
 c_\lambda=(1+\|\zeta_\lambda\|^2)^{-1/2},\qquad
 u_\lambda=c_\lambda(u_{0,\lambda}-\zeta_\lambda).
\]

[SchurNormalizedComparison.lean](../InfiniteZero/SchurNormalizedComparison.lean) and `SchurGroundEstimates` establish, without a smallness assumption,

\[
 \|u_\lambda\|=1,\quad
 \langle u_{0,\lambda},u_\lambda\rangle=c_\lambda\in(0,1],\quad
 0\le1-c_\lambda\le\|\zeta_\lambda\|^2,\quad
 \|u_\lambda-u_{0,\lambda}\|\le2\|\zeta_\lambda\|.
\]

The positive inner product fixes the **relative phase** with respect to the radial vector. It does not assert that the complex eigenfunction is pointwise positive, that independently chosen states already have this phase, or that this phase is continuous in `λ`.

With the preceding residual and `gλ = g₀λ`, the correction of the same certificate and its normalization coefficient satisfy

\[
 \|\zeta_\lambda\|\le\frac K{g_0}e^{-d\lambda},\quad
 1-c_\lambda\le\frac{K^2}{g_0^2}e^{-2d\lambda},\quad
 \|u_\lambda-u_{0,\lambda}\|\le\frac{2K}{g_0}e^{-d\lambda}.
\]

Setting `ηλ = −cλζλ` recovers the decomposition `uλ = cλu₀,λ + ηλ`, with `ηλ ⟂ u₀,λ` and `‖ηλ‖ ≤ ‖ζλ‖`. Normalization preserves the eigenvector graph by `normalizedSchurVector_mem_graph`. The compiled theorem `exists_atomicGroundVectors_exponential_comparison_of_radialData` applies this to the same concrete ground-state certificate. With constants fixed before `λ`, it supplies, for every sufficiently large coupling, two vectors `u,v : L2Space` such that

\[
 \begin{gathered}
 \|u\|=\|v\|=1,\qquad
 u\in\ker(A^0_\lambda-E^0_\lambda),\qquad
 v\in\ker(A_\lambda-E_\lambda),\\
 \|v-u\|\le C_Ve^{-d\lambda},\qquad
 \operatorname{Re}\langle u,v\rangle>0,\qquad
 \operatorname{Im}\langle u,v\rangle=0,
 \end{gathered}
\]

where `C_V = 2K/g₀`. The conclusion concerns vectors in the actual L² eigenspaces and chooses their relative phase. The arbitrary choice `canonicalAtomicState` is not identified with this aligned state without handling its phase factor, and no continuity of this choice in `λ` is asserted.

## Corollaries from the elementary conditions

[Remaining.lean](../InfiniteZero/Remaining.lean) exposes the two corollaries

- `CuspParameters.atomicGroundEnergy_exponential_comparison`;
- `CuspParameters.atomicGroundVectors_exponential_comparison`.

They require only `hp : p.BasicConditions` and retain exactly the two preceding conclusions. A004 supplies only radial spectral data, and A002 both realizations. Residual bounds, compression, Schur comparison, and normalization are proved in the preceding modules. These corollaries therefore depend on the classical admissions **A002+A004**, with no new comparison admission and no A003.

## Scope

These are **absolute exponential L²-norm estimates** and estimates on atomic energies. They do not supply a relative radial-tail asymptotic, a lower amplitude bound, a uniform pointwise estimate, sharp action rates, the weighted inverse, or oscillatory tunneling-cell asymptotics. Those obligations are separate from atomic spectral comparison.
