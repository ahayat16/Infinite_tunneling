# A004 — the radial ground state and semiclassical low levels

The remaining admission is
[`classical_radial_low_levels`](../InfiniteZero/ClassicalRadialLowLevels.lean).
It supplies the first two harmonic-approximation estimates and a positive
normalized radial ground state. Lean proves the oscillator-level ordering,
the resulting gap asymptotics, the conversion to the unscaled operator,
and the min-max inequality on the ground state's orthogonal complement.
The application to the explicit core retains its existing interface.

## Exact remaining assumption

Let `V : ℝ² → ℝ` satisfy
[`RadialSingleWell`](../InfiniteZero/RadialSingleWell.lean):

- `V` is smooth and compactly supported, and `V ≤ 0`;
- `V(0) < 0` and `V(0) < V(x)` for every `x ≠ 0`;
- `V(x) = V(|x|e₀)`, where `e₀ = (1,0)`;
- the signed radial profile `r ↦ V(re₀)` has second derivative `d > 0` at zero.

Set

\[
 A(x)=\tfrac12(-x_2,x_1),\qquad
 L_h=(-ih\nabla-A)^2+V.
\]

In Lean, `semiclassicalMagneticOperator V h` is defined as
`h²` times `magneticOperator 1 h⁻¹ V`, on the same operator domain.
The magnetic realization is the closure of the compactly supported smooth
test-function graph, as specified in
[A002](ADMISSIONS.md#a002--realization-of-the-magnetic-operator).

Let `e₁(h)` be the infimum of `Re⟨u,Lₕu⟩` over unit vectors in `D(Lₕ)`.
Let `e₂(h)` be the infimum of the real numbers `E` for which there is a
complex two-dimensional subspace `F ⊂ D(Lₕ)` satisfying
`Re⟨u,Lₕu⟩ ≤ E` for every unit vector `u ∈ F`.
These are `radialFirstSemiclassicalLevel` and
`radialSecondSemiclassicalLevel`.

Define the classical oscillator mode values by

\[
 M_d(n,m)=\sqrt{1+2d}\,(2n+|m|+1)-m,
 \qquad n\in\mathbb N_0,\quad m\in\mathbb Z.
\]

Here `μ₁(d)` is the infimum of all these values and `μ₂(d)` is the
infimum after excluding `(n,m) = (0,0)`. Their definitions are
`radialOscillatorGroundLevel` and `radialOscillatorSecondLevel`.
The connection of this mode family with the oscillator spectrum is
classical input; ordering the family is proved in Lean.

**A004 states that there exist `h₀ > 0` and `C > 0` such that, for every
`0 < h ≤ h₀`,**

\[
 |e_j(h)-V(0)-h\mu_j(d)|\le C h\sqrt h,
 \qquad j=1,2,
\]

and there exist a smooth function `φₕ : ℝ² → ℂ` and a vector
`uₕ ∈ D(Lₕ)` such that

\[
 \|u_h\|_2=1,\qquad L_hu_h=e_1(h)u_h,
 \qquad u_h=[\phi_h]_{L^2},
\]

with `φₕ` real, radial, and strictly positive at every point.
The constants are fixed before choosing `h`; the state may depend on `h`.
No continuity of that choice is required. The positivity predicate
[`IsPositiveRadial`](../InfiniteZero/RealRadialState.lean) means precisely
`φ(x) = (Re φ(|x|e₀) : ℂ)` and `0 < Re φ(x)` for every `x`.

```lean
theorem classical_radial_low_levels (V : Potential) (hV : RadialSingleWell V) :
    Nonempty (RadialLowLevelData V) := by
  sorry
```

## References and correspondence

Helffer–Kachmar,
[Quantum tunneling in deep potential wells and strong magnetic field revisited,
arXiv:2208.13030v5](https://arxiv.org/pdf/2208.13030v5), provide the
single-well hypotheses in (1.1), the positive normalized radial state in
Theorem 1.1(1–2), and the fixed-index harmonic approximation with
`O(h^(3/2))` error in Proposition 2.1. Apply the proposition at `j = 1,2`
and choose common constants. Section 2.2 identifies the limiting magnetic
oscillator with quadratic potential `(d/2)|x|²`. The relevant printed
pages are 1, 3, and 10–12. Only single-well results are used.

For the full oscillator mode formula, a direct reference is
Drigho-Filho–Kuru–Negro–Nieto,
[Superintegrability of the Fock-Darwin system,
arXiv:1703.06634](https://arxiv.org/pdf/1703.06634), Section 2.2,
equations (2.22)–(2.29), especially (2.27). In its notation, set
`ℏ = 1`, particle mass `= 1/2`, `eB/c = 1`, and spring constant `= d`.
Then `ωc = 2`, `ω = √(1+2d)`, and its energy formula is `M_d(n,m)`.
This spectral decomposition, including completeness, is the classical
oscillator input in A004.

The admitted statement combines these published spectral results; it is
not a verbatim copy of one theorem. Its smooth representative and concrete
operator domain use the usual smooth elliptic realization, also recorded
in A002. The remaining review consists of matching those realizations,
the stated radial hypotheses, and the cited oscillator spectrum.

## Deductions proved in Lean

For `h > 0`, the error term `h√h` equals `h^(3/2)`. Dividing the two
error estimates by `h` and using `√h → 0` gives

\[
 \frac{e_j(h)-V(0)}h\longrightarrow\mu_j(d)
 \quad(h\downarrow0).
\]

The scalar mode calculation proves that `(0,0)` is the unique ground
mode and `(0,1)` attains the first excited value:

\[
 \mu_1(d)=\sqrt{1+2d},\qquad
 \mu_2(d)=2\sqrt{1+2d}-1,\qquad
 \delta(V)=\mu_2(d)-\mu_1(d)=\sqrt{1+2d}-1>0.
\]

Indeed, the increase from the ground value is
`2nω + (|m|ω − m)`, where `ω = √(1+2d) > 1`. Every nonzero mode has
increase at least `ω−1`, with equality at `(0,1)`.

Set `k = 1/h`, `Hₖ = (-i∇−kA)²+k²V`, and

\[
 g(k)=k\bigl(e_2(1/k)-e_1(1/k)\bigr).
\]

Subtracting the two limits proves `g(k) → δ(V)`. Positive scalar
multiplication preserves the operator domain and scales both min-max
levels, so `k g(k)` is exactly the second min-max of `Hₖ` minus its
variational bottom. The same normalized ground vector is used for both
operators.

The complement inequality is also proved. Let `v` be a unit ground
vector of a self-adjoint operator, with energy `E₁`, and let `w` be a
unit domain vector orthogonal to `v`. The two vectors span a complex
two-dimensional domain subspace. On this span, self-adjointness and the
eigenvector equation cancel the mixed terms. Its largest Rayleigh
energy is therefore
`max(E₁, Re⟨w,Hw⟩) = Re⟨w,Hw⟩`, using the ground lower bound.
The definition of the second min-max gives
`E₂ ≤ Re⟨w,Hw⟩`. Homogeneity yields

\[
 E_2\|u\|_2^2\le\operatorname{Re}\langle u,Hu\rangle
 \quad\text{whenever }\langle v,u\rangle=0.
\]

A positive limiting gap supplies an eventual positive gap and a common
threshold. Together with the ground lower bound from unchanged A002,
this constructs `GroundStateCertificate` and then the existing
`RadialHarmonicData` interface.

| Verified step | Lean source |
| --- | --- |
| Ordering the oscillator modes and computing their gap | [RadialOscillatorLevels.lean](../InfiniteZero/RadialOscillatorLevels.lean) |
| From harmonic errors to limits, and from `h` to `k = 1/h` | [RadialHarmonicLimits.lean](../InfiniteZero/RadialHarmonicLimits.lean) |
| Scaling both operator min-max levels and the ground eigenvector | [SemiclassicalOperator.lean](../InfiniteZero/SemiclassicalOperator.lean) |
| Two-dimensional min-max argument and ground certificate | [OperatorSecondMinmax.lean](../InfiniteZero/OperatorSecondMinmax.lean) |
| Assembly of `RadialHarmonicData` | [RadialHarmonicAssembly.lean](../InfiniteZero/RadialHarmonicAssembly.lean) |

The declaration `classical_radial_harmonic` in
[Remaining.lean](../InfiniteZero/Remaining.lean) is now a proved assembly
from A004 and A002. It is no longer an admitted statement.

## Proved application to the explicit core

For the repository's radial core `v° = p.core`, only `r₀ > 0` is needed.
The subsequent application also fixes `b > 0`. The following steps have
Lean proofs:

| Step | Lean source |
| --- | --- |
| Radiality, strict minimum and `(v°)''(0) = 2/r₀²` | [CoreRadialHypotheses.lean](../InfiniteZero/CoreRadialHypotheses.lean) |
| All `RadialSingleWell` hypotheses for `V = v°/b²` | [RadialSingleWell.lean](../InfiniteZero/RadialSingleWell.lean) |
| `0 ≤ v°(x)+1 ≤ 2|x|²/r₀²` | [CoreQuadraticBound.lean](../InfiniteZero/CoreQuadraticBound.lean) |
| `atomicGroundEnergy b v° λ ≤ −λ²+Bλ` for every `λ > 0` | [RadialCoreVariationalBound.lean](../InfiniteZero/RadialCoreVariationalBound.lean) |
| Equality with the unit-field model at coupling `bλ` and potential `v°/b²` | [MagneticFieldScaling.lean](../InfiniteZero/MagneticFieldScaling.lean) |
| Eventual gap `≥ (b δ(V)/2)λ` from the positive limiting ratio | [MagneticGapThreshold.lean](../InfiniteZero/MagneticGapThreshold.lean) |
| Atomic state and test-function inequality from a certificate and A002 | [RadialGroundCertificate.lean](../InfiniteZero/RadialGroundCertificate.lean) |
| Common constants and threshold for `RadialCoreSpectralData b p` | [RadialCoreSpectralAssembly.lean](../InfiniteZero/RadialCoreSpectralAssembly.lean) |

The field conversion is the exact identity

\[
 (-i\nabla-b\lambda A)^2+\lambda^2v^\circ
 =(-i\nabla-(b\lambda)A)^2+(b\lambda)^2(v^\circ/b^2).
\]

It uses no spatial dilation and preserves the operator domain, energy,
eigenfunction and normalization. For `V = v°/b²`, choose
`γ = b δ(V)/2 > 0`. The positive limit of `g` supplies a threshold beyond
which `g(bλ) ≥ δ(V)/2`. A common positive threshold also ensures the
existence of the positive ground state, so all conclusions hold for
every `λ ≥ T`. All constants are fixed before choosing the coupling.

The declaration `radial_core_spectral_data` is a proved assembly from
A004 and A002; its
[`RadialCoreSpectralData`](../InfiniteZero/RadialCoreSpectralData.lean)
interface is unchanged. It provides the core energy bound and, for every
test function `u`,

\[
 \gamma\lambda\bigl(\|u\|_2^2-|\langle\phi,u\rangle|^2\bigr)
 \le q_{b,\lambda,v^\circ}(u)-E^\circ(\lambda)\|u\|_2^2.
\]

The orthogonal decomposition, cancellation of cross terms, and conversion
from the operator to the test-function form are proved in Lean, reusing
[AtomicGroundRankOne.lean](../InfiniteZero/AtomicGroundRankOne.lean).
The separate positive-ground field uses the same smooth positive
representative.

## Independent variational proof of the energy bound

Write `a = |x|²`. If `a ≤ r₀²/2`, then

\[
 1-\exp\!\left(-\frac{a}{r_0^2-a}\right)
 \le \frac{a}{r_0^2-a}\le\frac{2a}{r_0^2}.
\]

If `a ≥ r₀²/2`, the same upper bound follows from `v° ≤ 0`.
Together with `v° ≥ −1`, this proves the global quadratic comparison.

Choose a normalized smooth compactly supported function `η`; in Lean,
the nonzero core itself is normalized in L². For `λ > 0`, put

\[
 \eta_\lambda(x)=\sqrt\lambda\,\eta(\sqrt\lambda\,x),\qquad
 Q(x)=\frac{2}{r_0^2}|x|^2,\qquad C=q_{b,1,Q}(\eta).
\]

The proved magnetic dilation identity and quadratic comparison give
`mass ηλ = 1` and

\[
 q_{b,\lambda,v^\circ}(\eta_\lambda)
 \le\lambda(C-\lambda)\le-\lambda^2+(|C|+1)\lambda.
\]

Taking the variational infimum proves the bound with `B = |C|+1 > 0`,
for every positive coupling. This proof uses neither A004 nor A002 and
requires no existence of a ground eigenfunction.

## Scope

A004 concerns radial single wells. The nonradial construction, exterior
profile equations, Agmon estimates, cusp sources, hopping asymptotics,
and double-well spectral transfer are separate Lean arguments. They are
not conclusions assumed in `classical_radial_low_levels`.
