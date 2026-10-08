# Standard Landau resolvent and its physical normalization

Admission **A003** is
[`classical_standard_landau_resolvent`](../InfiniteZero/ClassicalLandauResolvent.lean).
It identifies the integral kernel of the closed free Landau operator at
Planck constant one. The passage from a smooth `L²` solution to the
closed operator domain, and all coupling and kernel scaling factors,
are proved in Lean. The existing public theorem
`free_landau_resolvent_kernel` is a proved consequence of A002 and A003.

## Exact remaining statement

For `B>0` and `ρ>0`, let

\[
 H_B=\left(-i\nabla-\frac B2x^\perp\right)^2,
 \qquad x^\perp=(-x_1,x_0),
\]

with the self-adjoint realization obtained by closing its graph on
`C_c^∞(ℝ²)`. In Lean this is `magneticOperator B 1 0`, with its fixed
operator domain. Set, off the diagonal,

\[
 G_{B,\rho}(x,y)=e^{-iB(x\wedge y)/2}\frac{B}{4\pi}
 \int_0^\infty
 \frac{\exp\!\left(-\rho t-\frac B4\coth(Bt)|x-y|^2\right)}
      {\sinh(Bt)}\,dt.
\]

A003 states: for every `U∈D(H_B)` and every smooth compactly supported
complex function `f`, if

\[
 (H_B+\rho)U=[f]_{L^2},
\]

then

\[
 U=\left[x\longmapsto\int_{\mathbb R^2}G_{B,\rho}(x,y)f(y)\,dy\right]_{L^2}.
\]

The predicate is
[`HasStandardLandauResolvent`](../InfiniteZero/StandardLandauResolvent.lean).
It uses `Represents` for equality almost everywhere and
`freeLandauKernel B 1 ρ` for the displayed kernel. The value assigned on
the diagonal does not affect this identity. The contract concerns
vectors already in the closed operator domain; it makes no smoothness
or maximal-domain assertion about `U`.

## Primary references

H. D. Cornean, S. Fournais, R. L. Frank, and B. Helffer,
*Sharp trace asymptotics for a class of 2D-magnetic operators*,
Annales de l'Institut Fourier **63** (2013), 2457–2513,
[DOI 10.5802/aif.2835](https://doi.org/10.5802/aif.2835),
equation **(B.21), printed p.2508**
([PDF p.53](https://www.numdam.org/item/10.5802/aif.2835.pdf#page=53)),
gives the heat kernel in precisely this symmetric gauge. Its negative
magnetic phase and prefactor agree with the formula above. Integrating
against `exp(−ρt)` gives the resolvent kernel. The same paper uses the
Laplace-transform representation for its differentiated resolvent on
printed p.2509.

B. Helffer and K. Pankrashkin, *Semiclassical reduction for magnetic
Schrödinger operator with periodic zero-range potentials and applications*,
[arXiv:0802.1414v2, equations (5.1)–(5.2), pp.11–12](https://arxiv.org/pdf/0802.1414v2#page=11),
state the heat kernel and its Laplace transform as a resolvent kernel
directly. Their operator uses Landau gauge, so its phase differs from
the symmetric-gauge phase used here.

Thus A003 is the standard resolvent consequence of the same-gauge
Mehler formula and the classical Laplace-transform identity; (B.21)
itself is a heat-kernel formula. The remaining classical input includes
identification with the closed operator and the integral representation.
The following natural-language proof records the sign, integrability,
and almost-everywhere conventions. The subsequent Lean reductions do
not require a change of gauge.

## Conventions and rescaling

Write `x=(x₀,x₁)`, `x⊥=(−x₁,x₀)`, and
`x∧y=x₀y₁−x₁y₀`. For `b,h>0`, the free semiclassical operator is

\[
 H_{b,h}=\left(-ih\nabla-\frac b2x^\perp\right)^2.
\]

Take its nonnegative self-adjoint realization on `L²(ℝ²)`, obtained by
closing the operator on `C_c^∞`. The repository fixes this graph explicitly;
its realization properties are the unchanged input A002. The domain
argument for smooth inhomogeneous solutions is proved below.

With `λ=1/h`, the repository's expression `magneticHamiltonian b λ 0` is
`h⁻² H_{b,h}`. More generally,

\[
 h^2\,\texttt{magneticHamiltonian}(b,\lambda,v)=H_{b,h}+v.
\]

The coordinates of `Plane := EuclideanSpace ℝ (Fin 2)` do carry the usual
Lebesgue measure: mathlib provides `PiLp.volume_preserving_ofLp` and
`PiLp.volume_preserving_toLp` in
`MeasureTheory/Measure/Haar/InnerProductSpace.lean`. Thus there is no
arbitrary Haar normalization to absorb into the factor `4π`.

Set `B=b/h`. Then `H_{b,h}=h² H_{B,1}`. Applying Mehler's formula with
field `B` and time `s=h²t` gives

\[
 Q_t(x,y)=\frac{b}{4\pi h\sinh(bht)}
  \exp\!\left(-\frac{ib}{2h}x\wedge y\right)
  \exp\!\left(-\frac{b}{4h}\coth(bht)|x-y|^2\right).
\]

The semigroup time is still `t`: the scalar exponential in the resolvent
will be `e^{-tE}`, not `e^{-tE/h}` at this stage.

A direct sign check is useful. For `P_x=−ih∇ₓ−(b/2)x⊥`, `r=x−y`, and a
function `f(r)`,

\[
 P_x\bigl(e^{-ibx\wedge y/(2h)}f(x-y)\bigr)
 =e^{-ibx\wedge y/(2h)}
   \left(-ih\nabla_r-\frac b2r^\perp\right)f(r).
\]

Indeed, `∇ₓ(x∧y)=−y⊥`. The opposite phase does not give this identity
for the repository's `−A` convention. For `f_t(r)=a(t)e^{-c(t)|r|²}`,
the heat equation becomes

\[
 \frac{a'}a=-4h^2c,\qquad c'=\frac{b^2}{4}-4h^2c^2.
\]

The values `a=b/(4πh sinh(bht))` and `c=b coth(bht)/(4h)` satisfy these
equations. As `t→0+`, they reproduce the free kernel
`(4πh²t)⁻¹ exp(−|r|²/(4h²t))`. This checks the sign, prefactor, and
initial condition; the identification with the semigroup of the closed
operator then uses uniqueness of the evolution in `L²`.

## Natural-language proof: integrating the semigroup

For `E>0`, the spectral calculus gives, in `L²`,

\[
 (H_{b,h}+E)^{-1}=\int_0^\infty e^{-tE}e^{-tH_{b,h}}\,dt.
\]

The scalar justification is `∫₀∞e^{-t(s+E)}dt=(s+E)⁻¹` for `s≥0`.
The bound `‖e^{-tH_{b,h}}‖≤1` gives strong integrability and the bound
`‖(H_{b,h}+E)⁻¹‖≤1/E`.

For `x≠y`, substituting `Q_t` and setting **`τ=ht`**, hence `dt=dτ/h`,
gives

\[
 (H_{b,h}+E)^{-1}(x,y)
 =e^{-ibx\wedge y/(2h)}K_{b,h,E}(|x-y|),
\]

\[
 K_{b,h,E}(r)=\frac{b}{4\pi h^2}
 \int_0^\infty\frac{1}{\sinh(b\tau)}
 \exp\!\left[-\frac1h\left(E\tau+
       \frac b4\coth(b\tau)r^2\right)\right]d\tau,
 \qquad r>0.
\]

This is exactly `landauKernel b h E r`, followed by
`freeLandauKernel b h E x y`. The second factor `h⁻¹` comes exclusively
from `dt=dτ/h`. The formula has no extra factor `2`, `h²`, or `λ²`.

## Integrability, the diagonal, and equality almost everywhere

For `r>0`, the integral converges: at `τ=0`, the Gaussian factor contains
`exp(−r²/(4hτ))`; at infinity, `1/sinh(bτ)` and `exp(−Eτ/h)` decay.
This off-diagonal integrability is already proved in
[LandauKernel.lean](../InfiniteZero/LandauKernel.lean).

At `r=0`, the integrand is asymptotic to `1/(bτ)` near zero. The improper
integral diverges. The resolvent kernel therefore has no canonical finite
value on `x=y`; its local singularity is logarithmic. One should not try
to prove a convergent integral formula on the diagonal.

In Lean, the Bochner integral is total: it equals zero for a nonintegrable
function. The current definition therefore chooses a finite value on the
diagonal. Proving precisely that this value is zero would require
formalizing nonintegrability at `r=0`, but this value does not enter the
contract. For each `x`, the singleton `{y=x}` has measure zero; changing
this value does not change any integral against a source. The diagonal
also has measure zero for the product measure.

A short argument controls spatial integrability without using a crude
`r⁻²` bound, which would be nonintegrable near zero in dimension two.
The spatial integral of the absolute value of the heat kernel is exactly

\[
 \int_{\mathbb R^2}|Q_t(x,y)|\,dy=\frac1{\cosh(bht)}\le1.
\]

After assigning an arbitrary value to `K(0)`, Tonelli gives

\[
 \int_{\mathbb R^2}K_{b,h,E}(|r|)\,dr
 =\int_0^\infty\frac{e^{-Et}}{\cosh(bht)}dt\le\frac1E.
\]

For a bounded source `F`, the integral
`∫ freeLandauKernel(x,y) F(y) dy` therefore converges absolutely for
every `x`. In particular, this holds for `F∈C_c^∞`. Fubini then identifies
this function with the resolvent applied to `F`, as an `L²` class. For
`F∈L²` only, domination by convolution with the radial `L¹` kernel,
Young's inequality, and density give a representation almost everywhere.
Both conclusions suffice for the Lean predicate, which requires **AE**
equality and does not select a pointwise spectral representative.

## Application to the effective atomic state

Suppose `λ>0`, `h=λ⁻¹`, `v` is real, smooth, and bounded, and `φ` is an
actual `L²` eigenfunction of the unscaled atomic operator, with energy
`e<0`. Set `E=−h²e>0`. Then

\[
 (H_{b,h}+v)\phi=-E\phi.
\]

For `d=(L,0)`, the repository's translations are

\[
 U_a\phi(x)=e^{-ibx\wedge a/(2h)}\phi(x-a),\qquad
 \phi^L=U_{-d}\phi,\qquad \phi^R(x)=\phi^L(-x).
\]

The gauge identity above proves that `U_a` commutes with the free
expression. Inversion transforms each covariant momentum into its
negative, and thus commutes with their sum of squares. These identities,
`C^∞` regularity, membership in `L²`, and conservation of mass are
proved in [MagneticCovariance.lean](../InfiniteZero/MagneticCovariance.lean).
Pointwise, this gives

\[
 (H_{b,h}+v^R)\phi^R=-E\phi^R,\qquad v^R(y)=v(d-y).
\]

The source `F_R=h⁻²v^Rφ^R` belongs to `L²`. For the constructed
potential, it is even smooth and compactly supported: the potential is
`C_c^∞`, and the eigenfunction has the smooth representative required by
the model. This property is proved by
`rightPhysicalSource_isTestFunction`, without assuming that `φ^R` has
compact support.

The passage to the closed domain is proved in
[MagneticInhomogeneousDomain.lean](../InfiniteZero/MagneticInhomogeneousDomain.lean).
If `u∈C^∞∩L²` satisfies the equation with `f∈C_c^∞`, then
`H_free u=f−λ²Eu∈L²`. Two integrations by parts give
`⟨H_free φ,u⟩=⟨φ,H_free u⟩` for every compactly supported smooth test
function `φ`. This equality is continuous in the graph pair
`(φ,H_free φ)`, so it extends to the closure of the test graph. It places
`u` in the adjoint domain with the required operator value.
Self-adjointness from A002 identifies this graph with the original
operator graph. The Lean argument uses only `graph_eq` and `selfAdjoint`
from the realization certificate; it does not use its eigenfunction
correspondence or assume a domain property for the atomic state.

The equation becomes `(H_{b,h}+E)φ^R=−h²F_R`, so

\[
 \phi^R(x)=-h^2\int_{\mathbb R^2}
     \texttt{freeLandauKernel}(b,h,E,x,y)F_R(y)\,dy
 \quad\text{for almost every }x.
\]

This is precisely `RightResolventRepresentation b v L λ E φ`.
With `φ=canonicalAtomicState p.b p.potential λ` and
`e=atomicGroundEnergy p.b p.potential λ`, the parameter `E` is
`scaledAtomicEnergy p λ`. The existence of this state and negativity of
its energy for all sufficiently large couplings are supplied separately
by [AtomicSourceRegime](../InfiniteZero/AtomicSourceRegime.lean) and the
atomic energy bounds. They do not follow from the kernel formula: the
application does use a normalized ground state, not the zero fallback
value of the canonical definition.

The argument requires neither simplicity, nor pointwise positivity of
`φ`, nor radial symmetry, nor convergence of an energy, nor large
separation `L`. The potential is real, but **the eigenfunction is not
assumed real**. The right state uses inversion, not complex conjugation.

## Proved passage to the physical resolvent interface

The existing contract `FreeLandauResolventKernel b λ E` states that,
for every `u∈C^∞∩L²` and `f∈C_c^∞`,

\[
 (\texttt{magneticHamiltonian}(b,\lambda,0)+\lambda^2E)u=f
 \Longrightarrow
 u(x)=h^2\int K_{b,h,E}(x,y)f(y)\,dy\quad\text{almost everywhere},
 \qquad h=\lambda^{-1}.
\]

This contract is now derived from A002 and A003. The proof uses
`B=bλ` and `ρ=λ²E`, without changing spatial coordinates:

\[
 \texttt{magneticHamiltonian}(b,\lambda,0)
 =\texttt{magneticHamiltonian}(b\lambda,1,0),
\]

\[
 h^2\,\texttt{freeLandauKernel}(b,h,E,x,y)
 =\texttt{freeLandauKernel}(b\lambda,1,\lambda^2E,x,y).
\]

The first equality follows by expanding the magnetic derivatives. For
the second, the substitution `τ=λt` in the defining proper-time integral
gives the Jacobian `λ`; the radial prefactor and magnetic phase then
agree exactly. This identity is proved for the total Bochner-integral
definitions, including their assigned diagonal values.

| Proved step | Lean source |
| --- | --- |
| Equality of the free differential expressions at fields `b,λ` and `bλ,1` | [StandardLandauResolvent.lean](../InfiniteZero/StandardLandauResolvent.lean) |
| Proper-time substitution, radial prefactor, phase, and source-integral scaling | [LandauResolventScaling.lean](../InfiniteZero/LandauResolventScaling.lean) |
| Smooth `L²` solution with `L²` Hamiltonian belongs to the closed graph | [MagneticInhomogeneousDomain.lean](../InfiniteZero/MagneticInhomogeneousDomain.lean) |
| Standard kernel formula implies the physical interface | [LandauResolventAssembly.lean](../InfiniteZero/LandauResolventAssembly.lean), `freeLandauResolventKernel_of_standard` |
| Instantiation of A002 and A003 | [Remaining.lean](../InfiniteZero/Remaining.lean), `free_landau_resolvent_kernel` |

The domain and scaling lemmas have no admitted dependencies. The
assembly takes the realization and standard kernel identity as explicit
hypotheses. `HasPositiveLandauResolvent b` retains the same public
interface over all `λ,E>0`.

What remains in A003 is the classical closed-operator kernel identity
at Planck constant one: Mehler's formula, its Laplace-transform resolvent
consequence, and identification of that inverse with the measurable
kernel. These are the classical arguments described above. Domain
membership of the smooth solution and the physical scaling factors
are no longer part of this admission.

The atomic application remains proved:
`rightResolventRepresentation_of_freeLandauResolventKernel` uses the
derived universal contract, covariance, compact support of the source,
and `E=−h²e`. `canonicalHopping_eq_source_of_resolvent` then proves
the two-source identity from this almost-everywhere representation and
the integrability of the cells. In `Main.lean`,
`LocalChannelAnalyticData.resolvent_representation` is a derived theorem,
not a field. Atomic existence at the cell threshold, positivity of `E`,
and the tunneling estimates are separate Lean proofs.
[ConstructedMainProof](../InfiniteZero/ConstructedMainProof.lean)
constructs the assembly data, and
[thm_main](../InfiniteZero/Remaining.lean) uses the three remaining
classical admissions A002–A004. A003 contains no estimate specific to
the constructed potential or its tunneling channels.
