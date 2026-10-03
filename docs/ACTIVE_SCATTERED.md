# Reducing the active cell to its incoming part

This chain controls the three active-cell terms containing the atomic correction. It retains the actual sources and the same states and coefficients as their L¹ estimates. The complex incoming–incoming asymptotic is proved in the [separate physical connection](INCOMING_PHYSICAL_ASYMPTOTIC.md). The [final assembly](../InfiniteZero/ConstructedMainProof.lean) now concludes [thm_main](../InfiniteZero/Remaining.lean), modulo A002–A005.

**Historical reduction milestone validation.** `bash scripts/check.sh` had completed successfully: 1874 theorems without admissions, 648 `assert_no_sorry` guards, four classical admissions, and one then-open final target. The transitive audit of both wrappers finds exactly A002+A004+A005, without A003 or `thm_main`. The inventory, DOT graph, and 256 blueprint entries were regenerated.

## Physical objects and quantifier order

Fix `p.BasicConditions`, explicit interfaces `HasInteriorEllipticEstimate`, `RadialCoreSpectralData p.b p`, magnetic realizations of the core and full potential, and `χ : CuspWeightCutoffs p`. Then fix L with `R<2L`, followed by

\[
 0<\beta_0<\beta,\qquad 2\beta<3\beta_0.
\]

One possible choice is `β₀=3β/4`. This changes neither the potential, its cutoffs, nor its parameter β. Constants and threshold are chosen before λ. They may depend on fixed L; uniformity over all large L is not asserted.

For each sufficiently large λ, the same normalized real, strictly positive radial core ground state φ and the same normalized full-potential ground state ψ supply

\[
 h=\lambda^{-1},\qquad c\in[1/2,1],\qquad \Gamma>0,\qquad
 u=c\varphi,\qquad \eta=\psi-c\varphi.
\]

The type retains C∞ regularity and L² membership of η, and `waveInner φ η = 0`. Thus c is not replaced by another scalar when comparing envelopes. The tail of the same φ is exactly

\[
 \varphi(x)=\Gamma K_b(h,E_h^\circ,\|x\|),\qquad \|x\|>r_0,
\]
\[
 E_h^\circ=-h^2E_{\rm core}(\lambda),\qquad
 E_h=-h^2E_{\rm full}(\lambda),\qquad
 A_h=2J_b(E_h^\circ,R)+J_b(E_h,2L-R).
\]

The bridge energy belongs to the full nonradial atom; both radial actions use the core energy. These energies are not identified. The assembly exports `E_h∈[1/2,1]`. The generic source-combination lemma requires no further core-energy bound.

Write Q(f,g) for the actual `sourcePairing` between `componentSource p h f 1` and `componentSource p h g 2`, with kernel `sourceKernel p.b L h E_h`. Its definition includes conjugation of the first source and outer factor `−h²`.

## From the exact kernel to three logarithmic costs

[ActiveCrossKernelBound](../InfiniteZero/ActiveCrossKernelBound.lean) proves on the cross closed supports

\[
 D:=2L-R\le\|z+w-2d\|\le2(L+\texttt{cuspSupportRadius}).
\]

The lower bound comes from both cusps’ horizontal inequalities; the upper bound from compact support. The uniform bound on the actual Landau kernel retains the entire action: for `E∈[1/2,1]` and `0<h≤1`,

\[
 K_b(h,E,\|z+w-2d\|)
 \le C h^{-2}\exp[-J_b(E,D)/h].
\]

The magnetic phase has modulus one. [ActiveCrossPairingBound](../InfiniteZero/ActiveCrossPairingBound.lean) bounds the absolutely convergent integral: the h² in Q cancels h⁻² exactly. For two integrable sources on opposite cusps,

\[
 |Q(F,G)|\le C e^{-J_b(E_h,D)/h}\|F\|_1\|G\|_1.
\]

Here F and G denote the sources themselves. Integrability is proved before integral manipulations. No additional positive bridge slope need be retained: the strictly positive slopes already in the source profiles have supplied the L¹ estimates of [AtomicSourceL1](../InfiniteZero/AtomicSourceL1.lean).

Choosing all three independent margins equal to β₀, these estimates are, for each cusp,

\[
 \|F^{\rm in}\|_1\le C_i\lambda^4c\Gamma
   e^{-\lambda J_b(E_h^\circ,R)}e^{-\beta_0\log^2\lambda},
\]
\[
 \|F^{\rm sc}\|_1\le C_s\lambda^6c\Gamma
   e^{-\lambda J_b(E_h^\circ,R)}e^{-2\beta_0\log^2\lambda}.
\]

The second cost contains a global response margin and a local margin spent in the real cusp integral. The strict losses needed for that integration are already handled in `AtomicSourceL1`; no additional coefficient β₀ is lost here.

[ActiveSourcePairingL1Bounds](../InfiniteZero/ActiveSourcePairingL1Bounds.lean) adds actions, powers, and logarithmic costs exactly. Its application to the same witnesses in [AtomicActiveScatteredBounds](../InfiniteZero/AtomicActiveScatteredBounds.lean) gives, with \(B_h=c^2\Gamma^2e^{-\lambda A_h}\),

\[
 |Q(u,\eta)|, |Q(\eta,u)|
 \le C_{\rm mix}B_h\lambda^{10}e^{-3\beta_0\log^2\lambda},
 \qquad
 |Q(\eta,\eta)|
 \le C_{\rm ss}B_h\lambda^{12}e^{-4\beta_0\log^2\lambda}.
\]

Powers 10 and 12 come from the available L¹ bounds; no optimal manuscript power is assumed. Factors ε and h⁻² already belong to the physical sources. This entire step uses sources on the real plane, without holomorphic continuation of η.

## Why the inverse saddle cost is exactly 2β

Set \(\ell=\log(1/h)\), and fix the scalar saddle parameters. The proved equation \(w+\Log w=\ell+d_*\), with \(\Re w\ge2\), gives

\[
 \Re w=\ell+\Re d_*-\log|w|\le\ell+\|d_*\|.
\]

The exact critical value is \(V_h=\beta(w^2+2w)-(k+1)^2/(4\beta)\). Taking real parts, the term \(-\beta(\Im w)^2\) and the subtracted constant are favorable:

\[
 \Re V_h\le\beta(\ell+\|d_*\|+1)^2.
\]

[SharpSaddleSize](../InfiniteZero/SharpSaddleSize.lean) identifies the inverse square of the Gaussian size exactly:

\[
 S_G(h)^{-2}=
 \frac{\Re w\ e^{2\Re V_h}}
 {(t_*^{k+1}\sqrt{\pi/\beta})^2}.
\]

Since eventually \(\Re w\le2\ell\), every fixed N and margin σ>0 give

\[
 S_G(h)^{-2}h^{-N}e^{-(2\beta+\sigma)\ell^2}\longrightarrow0,
 \qquad
 S_G(h)^{-2}h^{-N}\le e^{(2\beta+\sigma)\ell^2}
 \quad\text{eventually}.
\]

The proof reduces the upper bound to a constant times \(\ell e^{-\sigma\ell^2+A\ell}\). It retains leading coefficient 2β; the earlier coarse bound with 8β was insufficient for this comparison. No harmonic ground-state expansion or lower bound on Γ is involved: the same Γ² cancels on both sides.

For `k=2` and fixed complex slope `activeSaddleSlope p L`, taken at limiting energy 1, the size with the manuscript’s complex prefactor eventually satisfies \(S_{\rm Tex}^2\le S_G^2\le2S_{\rm Tex}^2\). [ActiveScatteredEnvelope](../InfiniteZero/ActiveScatteredEnvelope.lean) uses this comparison for the exact positive envelope

\[
 \mathfrak a_h=\varepsilon^2a^2c^2\Gamma^2
 \lambda^6\sqrt\lambda\ e^{-\lambda A_h}
 S_{\rm Tex}(h)^2.
\]

The saddle slope is fixed, while action A_h retains both moving effective energies. For every cost `q>2β` and power N, a threshold independent of c>0 and Γ>0 gives

\[
 B_h\lambda^N e^{-q\log^2\lambda}
 \le \frac{2}{\varepsilon^2a^2}\mathfrak a_h
       e^{-(q-2\beta)\log^2\lambda/2}.
\]

## Final exported statement and correspondence to P6.8

[SourcePairingAdditivity](../InfiniteZero/SourcePairingAdditivity.lean) proves, with integrability of all four terms,

\[
 I_{+-}(\psi)=Q(u,u)+Q(u,\eta)+Q(\eta,u)+Q(\eta,\eta).
\]

[AtomicActiveScatteredRelative](../InfiniteZero/AtomicActiveScatteredRelative.lean), through `exists_atomicGround_active_scattered_relative_of_radialData`, retains the same φ, ψ, c, Γ and exports, for \(\delta_\beta=(3\beta_0-2\beta)/2>0\),

\[
 |I_{+-}(\psi)-I_{+-}(u)|
 \le C\mathfrak a_h e^{-\delta_\beta\log^2\lambda},
\]

together with the same bound using `canonicalSourceCell p L λ 1 2` in place of ψ’s cell. This transfer uses uniqueness of the full ground state up to unit phase and exact cell invariance. It does not replace ψ with the canonical state in the positive decomposition `ψ=cφ+η`.

The proof first controls the sum of the three norms, using `λ¹⁰≤λ¹²` and weakening cost 4β₀ to 3β₀. The final physical API exports both differences above; it does not separately export the stronger doubled-margin version for the doubly scattered term. With `β₀=3β/4`, the common margin is `δβ=β/8`.

This realizes the original comparison of [`sublemma:P6-8-mixed`, `sublemma:P6-8-double`, and `sublemma:P6-8-envelope`](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L5483) through a variant using already-integrated L¹ norms, without adding a bridge slope. The margins 3β₀ and 4β₀ strictly exceed the envelope’s cost 2β and absorb every fixed polynomial loss.

The reduction alone does not supply the leading phase or nonzero coefficient of the incoming term. The coordinate identity of [CuspSourcePairingCoordinates](../InfiniteZero/CuspSourcePairingCoordinates.lean) is now complemented by [evaluation of the coupled integral](INCOMING_PHYSICAL_ASYMPTOTIC.md). The [canonical channels and hopping](ACTIVE_CHANNEL_ASYMPTOTIC.md) follow with relative remainder tending to zero; spectral connection and relative parity errors conclude the final theorem. The manuscript’s sharper rates do not follow from this reduction alone.

These modules add no admission. The atomic assembly takes classical interfaces as explicit arguments; it assumes neither a scattered-cell estimate, hopping asymptotic, nor analytic data already containing the target conclusion. The [classical wrapper](../InfiniteZero/ClassicalAtomicActiveScatteredRelative.lean) `atomicGround_active_scattered_relative hp hL hβ₀ hβ₀β hmargin` is compiled: it chooses χ and supplies A002, A004, and A005 to the conditional proofs. A003 and the final theorem are not used in its construction.

The compiled corollary `atomicGround_active_incoming_reduction hp hL` explicitly fixes `β₀=3β/4` and replaces the margin with `β/8`. Its only arguments are `BasicConditions` and `R<2L`: auxiliary margins are chosen in the proof before coupling.
