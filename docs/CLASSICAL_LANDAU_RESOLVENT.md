# The proved Landau resolvent formula

The former admission **A003** has been replaced by a proof.
[`classical_standard_landau_resolvent`](../InfiniteZero/ClassicalLandauResolvent.lean)
takes an explicit `IsMagneticRealization B 1 0` certificate and proves
the kernel formula from the concrete magnetic Gaussian. Its analytic
proof introduces no admission. The public theorem
`free_landau_resolvent_kernel` instantiates the realization certificate
using A002; its statement is unchanged.

## Statement and conventions

For `B>0` and `ρ>0`, let

\[
 H_B=\left(-i\nabla-\frac B2x^\perp\right)^2,
 \qquad x^\perp=(-x_1,x_0),
 \qquad x\wedge y=x_0y_1-x_1y_0.
\]

The operator is `magneticOperator B 1 0`, whose graph is prescribed by
the closure of the differential expression on `C_c^∞(ℝ²)`. Define, off
the diagonal,

\[
 G_{B,\rho}(x,y)=e^{-iB(x\wedge y)/2}\frac{B}{4\pi}
 \int_0^\infty
 \frac{\exp\!\left(-\rho t-\frac B4\coth(Bt)|x-y|^2\right)}
      {\sinh(Bt)}\,dt.
\]

For every `U∈D(H_B)` and `f∈C_c^∞(ℝ²;ℂ)`, the theorem proves

\[
 (H_B+\rho)U=[f]_{L^2}
 \quad\Longrightarrow\quad
 U=\left[x\longmapsto\int_{\mathbb R^2}G_{B,\rho}(x,y)f(y)\,dy\right]_{L^2}.
\]

The exact predicate is
[`HasStandardLandauResolvent`](../InfiniteZero/StandardLandauResolvent.lean).
`Represents` expresses equality almost everywhere, and
`freeLandauKernel B 1 ρ` is the displayed kernel. The assigned diagonal
value does not affect the source integral.

The Euclidean plane carries the usual Lebesgue measure. Mathlib's
`PiLp.volume_preserving_ofLp` and `PiLp.volume_preserving_toLp` connect
the Euclidean and Cartesian coordinate representations, fixing the
normalization used in the Gaussian integral.

## Proof from the explicit Gaussian

### Heat equation and endpoint limits

For `t>0`, set

\[
 Q_t(x,y)=\frac{B}{4\pi\sinh(Bt)}
   e^{-iB(x\wedge y)/2}
   \exp\!\left(-\frac B4\coth(Bt)|x-y|^2\right),
 \qquad T_t f(x)=\int Q_t(x,y)f(y)\,dy.
\]

These are `landauHeatKernel` and `landauHeatAction`. Differentiating
the Gaussian and its magnetic phase gives

\[
 \partial_t Q_t(x,y)=-H_{-B,y}Q_t(x,y).
\]

The field changes sign because `y` is the source variable. Bilinear
integration by parts against a compact smooth source `φ` therefore gives

\[
 \frac d{dt}T_t\varphi(x)=-T_t(H_B\varphi)(x).
\]

The phase has modulus one. Gaussian integration computes its absolute
spatial mass exactly:

\[
 \int |Q_t(x,y)|\,dy=\frac1{\cosh(Bt)}\le1.
\]

Writing the Gaussian as a normalized approximate identity proves
`T_t φ(x)→φ(x)` as `t→0+`; the phase equals one at `y=x`. The proof
uses mathlib's approximate-identity theorem for rescaled integrable
kernels, with the Gaussian normalization checked in Lean.

At the other endpoint,

\[
 |e^{-\rho t}T_t\varphi(x)|\le
 e^{-\rho t}\|\varphi\|_\infty\longrightarrow0
 \qquad(t\to\infty).
\]

### Absolute Fubini and the test-function inverse

The spatial mass estimate gives

\[
 \int_0^\infty\!\int_{\mathbb R^2}
 e^{-\rho t}|Q_t(x,y)|\,dy\,dt\le\frac1\rho.
\]

Multiplication by a bounded source preserves absolute integrability.
Fubini identifies `Rρ f = standardLandauResolventAction B ρ f` with

\[
 R_\rho f(x)=\int_0^\infty e^{-\rho t}T_t f(x)\,dt.
\]

For a compact smooth `φ`, the derivative formula becomes

\[
 \frac d{dt}\bigl(e^{-\rho t}T_t\varphi(x)\bigr)
 =-e^{-\rho t}T_t((H_B+\rho)\varphi)(x).
\]

Its right-hand side is integrable on positive time. The fundamental
theorem of calculus, with the endpoint limits above, proves the
pointwise identity

\[
 R_\rho((H_B+\rho)\varphi)=\varphi.
\]

The defining proper-time integral of `freeLandauKernel` agrees exactly
with the time integral of `e^{-ρt}Q_t`. Lean uses total Bochner integrals;
the algebraic identity includes their assigned diagonal values.
Absolute integrability in time and space supplies the almost-everywhere
integrability needed for Fubini. The argument uses no convergent
improper time integral on the diagonal.

### The L² estimate and closed-graph extension

Every row of `G` has absolute mass at most `1/ρ`.
Since `|G(x,y)|=|G(y,x)|`, the same bound holds for every column.
Weighted Cauchy–Schwarz proves

\[
 |R_\rho f(x)|^2\le\frac1\rho
   \int |G_{B,\rho}(x,y)|\,|f(y)|^2\,dy.
\]

Integration in `x`, Fubini, and the column bound establish both
membership in `L²` and

\[
 \|R_\rho f\|_2^2\le\rho^{-2}\|f\|_2^2.
\]

Linearity gives the estimate for differences of compact smooth sources.
Fix `f`, put `F=[f]` and `v=[Rρ f]`. For every compact smooth `φ`,
the test-function inverse gives

\[
 \|v-[\varphi]\|_2^2\le\rho^{-2}
 \|F-([H_B\varphi]+\rho[\varphi])\|_2^2.
\]

This inequality is a closed condition on a pair of `L²` vectors, so it
extends to the closure of the test graph. At a domain vector `U` with
`(H_B+ρ)U=F`, the right-hand side vanishes and `v=U`. The only field of
the realization certificate used here is `graph_eq`.

| Proved step | Lean source |
| --- | --- |
| Cartesian Gaussian integral | [PlaneGaussianIntegral.lean](../InfiniteZero/PlaneGaussianIntegral.lean) |
| Explicit kernel and spatial mass | [LandauHeatKernel.lean](../InfiniteZero/LandauHeatKernel.lean), [LandauHeatKernelBounds.lean](../InfiniteZero/LandauHeatKernelBounds.lean) |
| Magnetic heat equation | [LandauHeatEquation.lean](../InfiniteZero/LandauHeatEquation.lean) |
| Initial and infinite-time limits | [LandauHeatApproximation.lean](../InfiniteZero/LandauHeatApproximation.lean), [LandauHeatDecay.lean](../InfiniteZero/LandauHeatDecay.lean) |
| Time-integral formula and absolute Fubini | [LandauHeatLaplace.lean](../InfiniteZero/LandauHeatLaplace.lean), [LandauHeatSpacetime.lean](../InfiniteZero/LandauHeatSpacetime.lean) |
| Bilinear transposition and test-function inverse | [MagneticBilinearIntegrationByParts.lean](../InfiniteZero/MagneticBilinearIntegrationByParts.lean), [LandauHeatTestInverse.lean](../InfiniteZero/LandauHeatTestInverse.lean) |
| Weighted Cauchy–Schwarz and global Schur estimate | [IntegralKernelCauchySchwarz.lean](../InfiniteZero/IntegralKernelCauchySchwarz.lean), [IntegralKernelSchur.lean](../InfiniteZero/IntegralKernelSchur.lean), [LandauResolventL2.lean](../InfiniteZero/LandauResolventL2.lean) |
| Differences and extension to the closed graph | [LandauResolventActionLinearity.lean](../InfiniteZero/LandauResolventActionLinearity.lean), [LandauResolventCoreExtension.lean](../InfiniteZero/LandauResolventCoreExtension.lean) |

## Semiclassical normalization and smooth solutions

For `b,h>0`, write

\[
 H_{b,h}=\left(-ih\nabla-\frac b2x^\perp\right)^2,
 \qquad \lambda=h^{-1},\quad B=b\lambda,\quad\rho=\lambda^2E.
\]

The physical expression `magneticHamiltonian b λ 0` is `h⁻²H_{b,h}`.
It also equals `magneticHamiltonian (bλ) 1 0`. The proper-time change
of variables `τ=λt` proves

\[
 h^2\,\texttt{freeLandauKernel}(b,h,E,x,y)
 =\texttt{freeLandauKernel}(b\lambda,1,\lambda^2E,x,y).
\]

The Jacobian, prefactor, and magnetic phase are checked in
[LandauResolventScaling.lean](../InfiniteZero/LandauResolventScaling.lean).
The physical interface is therefore

\[
 (\texttt{magneticHamiltonian}(b,\lambda,0)+\lambda^2E)u=f
 \quad\Longrightarrow\quad
 u(x)=h^2\int\texttt{freeLandauKernel}(b,h,E,x,y)f(y)\,dy
 \quad\text{almost everywhere}.
\]

Here `u∈C^∞∩L²` and `f∈C_c^∞`. The equation gives `H_free u∈L²`.
[MagneticInhomogeneousDomain.lean](../InfiniteZero/MagneticInhomogeneousDomain.lean)
proves membership in the closed domain: integration by parts gives the
adjoint identity on tests, continuity extends it to the closed graph,
and self-adjointness identifies the adjoint with the original operator.
This uses the realization certificate's `graph_eq` and `selfAdjoint`.

[LandauResolventAssembly.lean](../InfiniteZero/LandauResolventAssembly.lean)
combines domain membership, the standard formula, and scaling.
[Remaining.lean](../InfiniteZero/Remaining.lean) supplies A002 to obtain
`free_landau_resolvent_kernel`.

## Application to the atomic state

For an atomic eigenfunction with unscaled energy `e<0`, set `E=−h²e>0`.
Magnetic translation and inversion give the right state `φᴿ` and its
potential `vᴿ`. These operations preserve smoothness, `L²` membership,
and the differential equation; see
[MagneticCovariance.lean](../InfiniteZero/MagneticCovariance.lean).
The physical source `Fᴿ=h⁻²vᴿφᴿ` is smooth and compactly supported,
as proved by `rightPhysicalSource_isTestFunction`. Its equation gives

\[
 (H_{b,h}+E)\varphi^R=-h^2F_R,
 \qquad
 \varphi^R(x)=-h^2\int
 \texttt{freeLandauKernel}(b,h,E,x,y)F_R(y)\,dy
 \quad\text{almost everywhere}.
\]

This is `RightResolventRepresentation`. For the canonical state, the
energy shift is `scaledAtomicEnergy p λ`. Existence of that state and
positivity of the shift follow from the separate spectral analysis,
using A002 and A004. The eigenfunction may be complex; the right state
is obtained by inversion.

`canonicalHopping_eq_source_of_resolvent` derives the two-source identity.
In `Main.lean`, `LocalChannelAnalyticData.resolvent_representation` is a
derived theorem. The kernel proof leaves no admission in this block;
the final construction retains A002 and A004.

## Classical references

The formula agrees with H. D. Cornean, S. Fournais, R. L. Frank, and
B. Helffer, *Sharp trace asymptotics for a class of 2D-magnetic
operators*, Annales de l'Institut Fourier **63** (2013), 2457–2513,
[DOI 10.5802/aif.2835](https://doi.org/10.5802/aif.2835).
Equation **(B.21), printed p.2508**
([PDF p.53](https://www.numdam.org/item/10.5802/aif.2835.pdf#page=53))
gives the heat kernel in the same symmetric gauge, with the same
negative magnetic phase and prefactor. The paper uses the
Laplace-transform representation for the differentiated resolvent on
printed p.2509.

B. Helffer and K. Pankrashkin, *Semiclassical reduction for magnetic
Schrödinger operator with periodic zero-range potentials and applications*,
[arXiv:0802.1414v2, (5.1)–(5.2), pp.11–12](https://arxiv.org/pdf/0802.1414v2#page=11),
give the heat kernel and its Laplace transform as a resolvent kernel
directly. They use Landau gauge, whose phase differs from the one above.
These references provide the classical context; the Gaussian
calculations, integral identities, and closed-graph extension described
here are proved in Lean.
