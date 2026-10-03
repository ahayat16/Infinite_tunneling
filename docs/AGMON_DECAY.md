# Global Agmon decay of atomic states

The results in [AtomicAgmonGlobal.lean](../InfiniteZero/AtomicAgmonGlobal.lean) are proved without admissions. They give an initial absolute exponential decay estimate for actual eigenfunctions, both for the radial core and for the constructed nonradial potential.

## Statement and quantifiers

Under `p.BasicConditions`, there exist constants `C > 0` and `d > 0`, chosen **before** the coupling `λ`, energy `E`, and state `φ`, such that

\[
 \lambda>0,\quad E\le-\frac34\lambda^2,\quad
 H_\lambda(p.\mathrm{potential})\phi=E\phi,\quad
 \|\phi\|_2^2=1
 \quad\Longrightarrow\quad
 \int_{\|x\|\ge4r_0}|\phi(x)|^2\,dx
 \le \frac{C}{\lambda^2}e^{-2d\lambda}.
\]

This is `exists_atomicPotential_agmon_tail`. The eigenvalue equation is the repository’s `IsEigenfunction` predicate: smoothness, membership in `L²`, and the pointwise differential equation. No global integrability of derivatives or energy density is assumed. Normalization is the real integral `mass φ = 1`.

`exists_atomicCore_agmon_tail` gives exactly the same bound for `p.core`. It assumes only `0 < p.r₀` and allows any real constant field `b`. Its constants are chosen before `b`, `λ`, `E`, and `φ`.

The factored proof `exists_atomicAgmon_tail_bound` treats a continuous potential `V` satisfying the explicit margin

\[
 \|x\|\ge r_0\quad\Longrightarrow\quad
 \frac{\lambda^2}{4}\le\lambda^2V(x)-E.
\]

Both concrete specializations are proved: for the full potential, the bound `V > −1/2` outside the core and the assumption on `E` give this margin; for the core, `V = 0` for `‖x‖ ≥ r₀` suffices. Thus the final result does not leave this margin as a new obligation for either potential.

## Fixed cutoff and weight

The exterior cutoff `σ = p.atomicOuterCutoff hr₀`, constructed in [AtomicLocalizationCutoffs.lean](../InfiniteZero/AtomicLocalizationCutoffs.lean), is smooth, satisfies `|σ| ≤ 1`, vanishes on the ball of radius `2r₀`, and equals one from radius `3r₀` onward. It comes from the cosine of a smooth bump and belongs to the IMS partition already used for atomic coercivity. There is a fixed constant `C_IMS > 0` such that

\[
 |\nabla\sigma|^2\le C_{\mathrm{IMS}}.
\]

In [AtomicAgmonWeight.lean](../InfiniteZero/AtomicAgmonWeight.lean), a second bump `ζ` equals one up to radius `3r₀` and zero from radius `4r₀` onward. A fixed bound `C_b > 0` for its two partial derivatives allows us to set

\[
 d=\frac1{8C_b}>0,\qquad
 F_\lambda(x)=d\lambda(1-\zeta(x)).
\]

For `λ ≥ 0`, the lemmas `atomicAgmonWeight_contDiff`, `atomicAgmonWeight_le`, `atomicAgmonWeight_zero`, `atomicAgmonWeight_eq_height`, and `atomicAgmonWeight_gradient_le` establish

\[
 \begin{gathered}
 F_\lambda\in C^\infty,\qquad 0\le F_\lambda\le d\lambda,\qquad
 |\nabla F_\lambda|^2\le\frac{\lambda^2}{16},\\
 F_\lambda=0\quad(\|x\|\le3r_0),\qquad
 F_\lambda=d\lambda\quad(\|x\|\ge4r_0).
 \end{gathered}
\]

The weight also vanishes where `|∇σ|² ≠ 0`. The exact identity `exp_atomicAgmonWeight_sq_mul_outer_gradient` therefore gives, at every point,

\[
 e^{2F_\lambda}|\nabla\sigma|^2=|\nabla\sigma|^2.
\]

All these constructions require only `r₀ > 0`. Neither the bump nor `C_b`, `d`, or `C_IMS` is chosen after `λ`.

## From the local identity to the global inequality

Integration by parts is first performed with compact cutoffs on the smooth eigenfunction. The local weighted result leaves a margin

\[
 \lambda^2 V-E-2|\nabla F_\lambda|^2
 \ge\frac{\lambda^2}{4}-2\frac{\lambda^2}{16}
 =\frac{\lambda^2}{8}
\]

on the nonzero support of `σ`, which is outside the core.

The theorem `magnetic_agmon_bounded_weight` in [MagneticAgmonBounded.lean](../InfiniteZero/MagneticAgmonBounded.lean) then actually removes the spatial cutoff. It applies the local inequality to `ηₙ = σ κₙ`, where `κₙ` is a smooth compact exhaustion. At each fixed point, `κₙ` is identically one in a neighborhood for sufficiently large `n`; its derivatives then vanish there. Its squared gradient norm is bounded by a constant divided by the squared radius, uniformly over the chosen radii.

For each fixed `λ`, the weight satisfies `e^{2Fλ} ≤ e^{2dλ}`. The weighted-mass and cutoff-error densities are therefore dominated uniformly in `n` by a constant times the integrable function `|φ|²`. Dominated convergence applies to both sides of the inequality. The limit concerns these mass and error integrals; it assumes no global integral of the differential energy of `φ`.

This gives

\[
 \frac{\lambda^2}{8}\|\sigma e^{F_\lambda}\phi\|_2^2
 \le 2\int e^{2F_\lambda}|\nabla\sigma|^2|\phi|^2
 =2\int |\nabla\sigma|^2|\phi|^2
 \le2C_{\mathrm{IMS}}.
\]

Integrability of the final density is proved using its bounded multiplier and `φ ∈ L²`. The same method proves `σ e^{Fλ} φ ∈ L²`. The order matters: remove the exhaustion at fixed `λ`, then use a final estimate with constants independent of `λ`. Domination uniform in `λ` is not required.

## Extracting the tail and scope

The lemma `exists_atomicAgmon_weighted_mass_bound` gives

\[
 \|\sigma e^{F_\lambda}\phi\|_2^2
 \le \frac{16C_{\mathrm{IMS}}}{\lambda^2}.
\]

On `‖x‖ ≥ 4r₀`, both `σ = 1` and `Fλ = dλ` hold. Integral comparison, with integrability proved, yields

\[
 e^{2d\lambda}\int_{\|x\|\ge4r_0}|\phi(x)|^2\,dx
 \le\|\sigma e^{F_\lambda}\phi\|_2^2.
\]

One can therefore choose `C = 16C_IMS`. The coefficient `λ⁻²` and factor `exp(−2dλ)` are those of the Lean conclusion, for the actual exterior probability integral.

The energy condition remains explicit in these theorems for general eigenstates. For actual ground states, the separate connection uses the energy bound `E₀(λ) ≤ −λ²+Bλ`, obtained from radial spectral data, then chooses in particular `λ ≥ 4B`. This does not change the Agmon proof; it supplies its energy hypothesis at large coupling.

This connection is formalized in [AtomicGroundAgmon.lean](../InfiniteZero/AtomicGroundAgmon.lean): `exists_atomicGround_agmon_tail_of_radialData` obtains the same constants `C,d` for all normalized ground states of the core and full potential, with a common threshold. Its corollary applies the bound to the canonical ground state and simultaneously proves that it is an actual ground state. In [Remaining.lean](../InfiniteZero/Remaining.lean), `CuspParameters.canonicalAtomicState_agmon_tail` supplies this result from `BasicConditions` alone, modulo A002 and A004. These admissions enter the construction of the state and its energy regime; the decay proof itself adds no admission.

This estimate is **absolute exponential decay** outside a fixed ball. It gives neither the sharp rate governed by radial and bridge actions, nor relative atomic-source asymptotics, their amplitudes, or the oscillating sign of hopping. These more precise tunneling-theorem obligations remain separate.

## Verification

`AtomicAgmonWeight` and `AtomicAgmonGlobal` compile without warnings. The targeted audit of the weight results, weighted mass, and both concrete tails finds only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or new Agmon/global-integrability axiom was introduced.
