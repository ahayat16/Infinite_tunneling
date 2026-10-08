# Absolute and relative bounds for the seven inactive cells

The seven real bounds, their application to the actual atomic state, and their transfer to the canonical state are compiled in [InactiveCellL1Bounds](../InfiniteZero/InactiveCellL1Bounds.lean), [AtomicInactiveCells](../InfiniteZero/AtomicInactiveCells.lean), and [ClassicalAtomicInactiveCells](../InfiniteZero/ClassicalAtomicInactiveCells.lean). Their relative comparison with the Gaussian envelope is now compiled in [AtomicInactiveRelative](../InfiniteZero/AtomicInactiveRelative.lean), with its [classical wrapper](../InfiniteZero/ClassicalAtomicInactiveRelative.lean). The three relative wrappers depend on A002+A004, without A003 or `thm_main`. The final results `elementaryPotential_main` and `thm_main` have been proved modulo A002–A004; see the [current status](STATUS.md) and [final audit](STATEMENT_AUDIT.md).

## Physical statement and order of choices

Fix `p.BasicConditions`, a geometric certificate `cert : p.SeparationCertificate`, then `L≥cert.L₀`. Set

\[
 h=\lambda^{-1},\quad D=2L-R,\quad \delta=\frac{bR^2}{64},\qquad
 E_h=-h^2E_{\rm full}(\lambda),\quad E_h^\circ=-h^2E_{\rm core}(\lambda),
\]
\[
 A_h=2J_b(E_h^\circ,R)+J_b(E_h,D).
\]

The kernel energy between both sources belongs to the full potential; both radial actions use the core energy. Both energies eventually lie in `[1/2,1]`, but are never identified.

`atomicGround_inactive_cells hp cert hL` chooses `C,T>0` before λ. For each `λ≥T`, the same positive radial core state φ, full ground state ψ, `c∈[1/2,1]`, and `Γ>0` satisfy the exact tail `φ(x)=ΓK(b,h,E°h,‖x‖)` for `‖x‖>r₀`, and, for each of the seven pairs other than `(1,2)` and `(2,1)`,

\[
 |I_{ij}(\psi)|\le C(\Gamma^2+1)\lambda^{10}
                         e^{-\lambda(A_h+31\delta)}.
\]

The same bound is supplied for `canonicalSourceCell p L λ i j`. Constants may depend on fixed L; the statement does not choose a single C for all `L≥L₀`. The states and Γ precede all seven indices.

The exported type retains only `c∈[1/2,1]`: it contains neither an identity between c and state overlap nor the decomposition `ψ=cφ+η`. Thus no identification of this coefficient with that of a later active asymptotic is claimed here. The scalar relative comparison, however, holds for every real `c≥1/2`.

The result under explicit data is `exists_atomicGround_inactive_cells_of_radialData`. The public wrapper uses only A002 and A004: magnetic realization and radial semiclassical harmonic approximation. Sobolev point evaluation, the interior elliptic estimate, and its uniform dependence on coefficient bounds are proved in Lean. Original source estimates and geometric margins are proved. A003 is not used.

## Proof through L¹ sources and action margins

The [L¹ source bounds](CUSP_SOURCE_L1.md) give, for the same ψ,

\[
 \|F_0\|_1\le C_0\lambda^2,\qquad
 \|F_i\|_1\le S\Gamma\lambda^6e^{-\lambda J_b(E_h^\circ,R)}
 \quad(i=1,2).
\]

The additional log-flat cusp-source factor is bounded by one here. Inactive cells have a strictly positive margin at scale `1/h`, sufficient for this absolute bound.

[InactiveKernelBounds](../InfiniteZero/InactiveKernelBounds.lean) bounds the actual Landau kernel on the supports with arbitrary action loss η. Take `η=δ`. The margins before this loss are:

| Supports | Count | Margin after adding source actions |
| --- | ---: | ---: |
| core–core | 1 | `32δ` |
| core–cusp, in both orders | 4 | `32δ` |
| same cusp | 2 | `48δ` |

This leaves `31δ` in the first five cases and `47δ` in the last two, weakened to the common margin `31δ`. Certified separation keeps the kernel arguments strictly away from zero.

The actual complex-integrand bound gives

\[
 |I_{ij}|\le h^2\,\sup_{\mathrm{supports}}|K_h^{E_h}|\,
                       \|F_i\|_1\|F_j\|_1.
\]

This `h²` is the factor in `sourcePairing`, with no added renormalization. To unify all seven cases, use `λ≥1`, set `Q=C₀+S+1`, and assign source coefficients `(1,Γ,Γ)` and actions `(0,J(E°h,R),J(E°h,R))`. Each coefficient product is bounded by `Γ²+1`, and

\[
 h^2\lambda^6\lambda^6=\lambda^{10}.
\]

The source exponentials reconstruct action A_h exactly. This proves `exists_inactiveCell_L1_bound`, with constant `KQ²`. `norm_inactiveCells_le_of_bound` then bounds the norm of the seven-term sum by seven times their bound; `exists_inactiveCells_L1_bound` absorbs that factor into the constant. [InactiveCellNormSum](../InfiniteZero/InactiveCellNormSum.lean) also defines the **sum of the seven norms**, `inactiveCellNormSum`, equal to the double index sum excluding both active cells. `inactiveCellNormSum_le_of_bound` bounds it by seven times the individual bound. The relative result below supplies this sum, not just the norm of the complex sum.

## The canonical state’s phase cancels exactly

[SourcePhaseInvariance](../InfiniteZero/SourcePhaseInvariance.lean) proves that multiplying ψ by a scalar z of norm one multiplies each source by z. Its two occurrences in the integrand give `conj(z)z=1`. Thus the entire complex cell is unchanged before any estimate.

Already-established simplicity of the full ground state identifies every normalized ψ with the canonical state up to such a phase. The lemma `canonicalSourceCell_eq_sourceCell` therefore transfers each exact bound. It imposes neither pointwise reality of ψ nor continuity of a phase choice, and does not rephase the positive radial reference or its coefficient Γ.

## Proved relative Gaussian comparison

[ActiveSaddleEnvelope](../InfiniteZero/ActiveSaddleEnvelope.lean) fixes the complex slope, independent of λ,

\[
 c_* = \alpha-i\theta,\qquad
 \alpha=\tfrac12\bigl(J_b'(1,R)+J_b'(1,2L-R)\bigr)>0,\qquad
 \theta=\tfrac{\sqrt3}{2}bL.
\]

These are `Geometry.activeActionSlope p.b 1 p.R L` and `Geometry.phaseSlope p.b L`. Derivatives are radial, and the energy is fixed at its limit 1. In contrast, action A_h retains exactly the two distinct effective energies defined above.

With `w=logFlatSaddleRoot β 2 tStar c* h` and critical value f_c, the positive scalar prefactor is

\[
 S_{\rm G}(h)=t_*^3\sqrt{\frac{\pi}{\beta\Re w}}\,e^{-\Re f_c}.
\]

The exact real definition `activeSaddleEnvelope p L λ c Γ` is

\[
 \mathfrak a_{\rm G}
 =\varepsilon^2a_q^2c^2\Gamma^2\lambda^6\sqrt\lambda\,
    e^{-\lambda A_h}S_{\rm G}(\lambda^{-1})^2.
\]

The code uses `λ^6 * Real.sqrt λ`, namely λ to power 13/2 for positive λ. The constant factors `k_p² k_b B_s²` in the TeX leading coefficient are not part of this envelope. Eventual positivity is proved with a threshold fixed before coefficients c and Γ.

[RelativeNormalizationRatio](../InfiniteZero/RelativeNormalizationRatio.lean) uses the proved lower bound `Γ≥ch²` for **every tail coefficient of the same radial state**. For `λ≥1` and `Γ⁻¹≤Cλ²`, it gives

\[
 \frac{\Gamma^2+1}{\Gamma^2}\le(1+C^2)\lambda^4,\qquad
 \frac{\Gamma^2+1}{c^2\Gamma^2}\le4(1+C^2)\lambda^4
 \quad(c\ge1/2).
\]

The loss is `h⁻⁴`, rather than `h⁻³` from the TeX’s `Γ≳h³ᐟ²`. This polynomial difference is compatible with a strict action margin; it does not prove the manuscript’s sharper lower bound.

[SaddleNormalizationIdentity](../InfiniteZero/SaddleNormalizationIdentity.lean) also establishes, for the scalar model and a root with positive real part, the exact identity

\[
 \|\mathrm{normalizer}\|\,\mathrm{leadingSize}
       =t_*^{k+1}\sqrt{\pi/\beta}.
\]

For `β,t*>0`, a fixed nonzero complex slope, `a>0`, and integer N fixed before h, it eventually deduces `leadingSize⁻² h⁻ᴺ exp(−a/h) ≤ exp(−a/(2h))`. This retains half the exponential margin.

After division by the envelope, powers of λ cost `λ^(10+4−13/2)=λ^(15/2)≤λ⁸`. The proof directly uses integer powers and `sqrt λ≥1`. It weakens margin `31δ` to `30δ`, then applies absorption with **N=8** and `a=30δ`, retaining `15δ`. Fixed factors `ε²a_q²` are strictly positive and enter the constant. No upper bound on Γ is needed.

`exists_atomicGround_inactive_relative_of_radialData` applies the universal quotient bound to the **same φ and Γ** as the absolute physical bounds. It also retains ψ, c, the exact tail, and both energy intervals. With constants C,T chosen before λ, it supplies

\[
 \sum_{(i,j)\notin\{(1,2),(2,1)\}}|I_{ij}(\psi)|
 \le C\mathfrak a_{\rm G}e^{-15\delta\lambda},
\]

together with the same sum for the canonical state and all seven individual bounds. The factor seven is absorbed into C. The wrapper `atomicGround_inactive_relative hp cert hL` uses only A002 and A004; the theorem under explicit interfaces has no admission.

## Comparison with the TeX prefactor

[SaddleEnvelopeComparison](../InfiniteZero/SaddleEnvelopeComparison.lean) is compiled and audited. It defines `logFlatSaddleTexLeading` with the principal complex square root of `π/(β(1+w))`, proves its norm is `logFlatSaddleTexSize`, and establishes for the **same root w**

\[
 \frac{S_{\rm G}(h)^2}{S_{\rm TeX}(h)^2}
 =\frac{|1+w|}{\Re w}\longrightarrow1.
\]

`eventually_logFlatSaddleLeadingSize_sq_bounds` explicitly gives `0<S_TeX` and `S_TeX²≤S_G²≤2 S_TeX²`. This scalar comparison is therefore already proved; the two prefactors are not declared equal.

The physical assembly [ActiveSaddleEnvelopeComparison](../InfiniteZero/ActiveSaddleEnvelopeComparison.lean) and [AtomicInactiveRelativeTex](../InfiniteZero/AtomicInactiveRelativeTex.lean) is **compiled**, as is its [classical wrapper](../InfiniteZero/ClassicalAtomicInactiveRelativeTex.lean). It multiplies both sizes by the same coefficients and action, spending only a factor two in the relative constant. No new state or Γ is chosen. The theorem `exists_atomicGround_inactive_relative_tex_of_radialData` and wrapper `atomicGround_inactive_relative_tex` therefore give the seven bounds and both sums of norms with the complex-Hessian envelope `activeSaddleTexEnvelope`, still at rate `exp(−15δλ)`.

The [universal canonical version](../InfiniteZero/CanonicalInactiveRelative.lean) is also compiled: it concerns the tail coefficient of **every supplied normalized positive radial state**, and **every `c≥1/2`**. [RadialCoreCoefficientUniqueness](../InfiniteZero/RadialCoreCoefficientUniqueness.lean) proves equality of the positive states and then their Γ coefficients. If c₀ is the existential result’s coefficient, `c₀≤1≤2c` gives `c₀²≤4c²`; changing the envelope therefore costs only four in the constant. This API allows reuse of witnesses from a subsequent active proof without reselecting them.

This block deduces no active-cell leading asymptotic, identification of coefficient c with overlap, oscillating hopping amplitude, or double-well spectral conclusion.
