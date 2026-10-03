# Classical identification of the Landau resolvent

Documentary and mathematical verification dated September 17, 2026. This
document justifies the classical admission **A003**,
`free_landau_resolvent_kernel`, in
[Remaining.lean](../InfiniteZero/Remaining.lean). Its universal contract is
defined in
[LandauResolventBridge.lean](../InfiniteZero/LandauResolventBridge.lean);
it connects the free differential expression with its actual resolvent
kernel. The application to `RightResolventRepresentation` is proved in
the same module. This document provides a precise reference and the
natural-language proof of the classical identification; it does not
replace its future Lean proof.

**Conclusion: the phase and prefactor of the current kernel are correct**
for the repository's conventions. The kernel on the diagonal must be
treated as a measurable representative, and the operator domain and the
almost-everywhere integral representation must be justified separately.
The atomic wave function may be complex; no real-valuedness assumption is
needed.

## Verified primary reference

H. D. Cornean, S. Fournais, R. L. Frank, and B. Helffer,
*Sharp trace asymptotics for a class of 2D-magnetic operators*,
Annales de l'Institut Fourier **63** (2013), 2457–2513,
[DOI 10.5802/aif.2835](https://doi.org/10.5802/aif.2835).
Equation **(B.21), printed page 2508**, in the proof of Proposition B.9,
gives the heat kernel for
`H = (−i∇−A)²`, `A(x)=b(−x₂,x₁)/2`, with the negative phase
`exp(−ib x∧y/2)` and coefficient `b/(4π sinh(bt))`.
The passage to the resolvent by integrating the semigroup is also used on
page 2509.
[Published PDF, page 2508](https://www.numdam.org/item/10.5802/aif.2835.pdf#page=53).
The PDF was consulted: page 53 of the file corresponds to page 2508 of the
article. The published version fixes the pagination reference here.

The calculations below directly check the changes of scale and spell out
the argument adapted to the repository's definitions.

## Conventions and rescaling

Write `x=(x₀,x₁)`, `x⊥=(−x₁,x₀)`, and
`x∧y=x₀y₁−x₁y₀`. For `b,h>0`, the free semiclassical operator is

\[
 H_{b,h}=\left(-ih\nabla-\frac b2x^\perp\right)^2.
\]

Take its nonnegative self-adjoint realization on `L²(ℝ²)`, obtained by
closing the operator on `C_c^∞`. This choice of realization is a classical
operator-theoretic fact to be justified in the Lean bridge; a differential
formula alone does not suffice to define the closed domain.

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

## Integrating the semigroup

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

The passage to the closed domain is included in the universal classical
result: if `u∈C^∞∩L²` satisfies the equation with `f∈C_c^∞`, then
`H_free u=f−λ²Eu∈L²` in the distributional sense. Thus `u` belongs to
the maximal domain. Essential self-adjointness of the free Hamiltonian
identifies this domain with that of its closure on `C_c^∞`; see the
[classical justification of the realization](CLASSICAL_OPERATOR_REALIZATION.md),
in particular Shubin, the beginning of Section 5 and Theorem 5.2. This
argument is what permits the application of the resolvent to the
classical solution. There is no need to admit a special covariance
property on the domain of the atomic state.

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

## Admitted contract and precise formalization boundary

The contract `FreeLandauResolventKernel b λ E` is stated universally:
for all `u∈C^∞∩L²` and `f∈C_c^∞`,

\[
 (\texttt{magneticHamiltonian}(b,\lambda,0)+\lambda^2E)u=f
 \Longrightarrow
 u(x)=h^2\int K_{b,h,E}(x,y)f(y)\,dy\quad\text{almost everywhere},
 \qquad h=\lambda^{-1}.
\]

The factor `h²` follows from
`magneticHamiltonian(b,λ,0)+λ²E = h⁻²(H_{b,h}+E)`.
The natural-language proof is to pass to the closed domain using the
maximal-domain argument above, multiply the equation by `h²`, then apply
the positive inverse identified through Mehler's formula and the Laplace
transform. Strict positivity of `E` ensures invertibility and uniqueness
of the `L²` solution. The signs, constants, integrability, and
almost-everywhere equality are checked in the preceding sections.

The declaration `free_landau_resolvent_kernel` admits exactly this
contract for `b,λ,E>0`. `HasPositiveLandauResolvent b` collects this same
interface over all `λ,E>0`, without any atomic data. There is no `sorry`
specific to the constructed potential or its cells in this bridge.

The repository's integral definitions and phase calculations are already
checked by Lean. `canonicalHopping_eq_source_of_resolvent` then proves
the two-source identity from this AE representation and the integrability
of the cells. The classical part collected in A003 breaks down as
follows:

1. Identify the semigroup of the closure of the free graph with Mehler's
   formula.
2. Obtain its positive inverse through the Laplace transform.
3. Identify this inverse with the measurable kernel, disregarding the
   diagonal.
4. Identify the maximal domain with the domain of the closure and pass
   between the unscaled operator and `h⁻²H_{b,h}`.

The application to the atomic state is **proved**:
`rightResolventRepresentation_of_freeLandauResolventKernel` uses the
universal contract, covariance, the smooth compactly supported source,
and `E=−h²e`. In `Main.lean`,
`LocalChannelAnalyticData.resolvent_representation` is a derived theorem,
not a field. Atomic existence starting at the cell threshold, positivity
of `E`, and the tunneling estimates are proved by the original
analysis. [ConstructedMainProof](../InfiniteZero/ConstructedMainProof.lean)
constructs the assembly data; [thm_main](../InfiniteZero/Remaining.lean)
is compiled modulo A002–A005. The classical resolvent identification
described above remains precisely admission A003, with no tunneling-specific
estimate added to its contract.
