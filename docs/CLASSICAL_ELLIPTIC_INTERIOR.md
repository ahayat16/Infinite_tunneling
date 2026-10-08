# Proved Sobolev point evaluation and interior elliptic estimates

Point evaluation by the local `H²` norm in dimension two and the uniform
interior elliptic estimate are proved in Lean. Neither result has an
admitted dependency. The former admission A005 has been eliminated.

The point estimate is
[`coordinateH2PointEvaluation`](../InfiniteZero/CoordinatePointEvaluation.lean).
The public theorems
[`classical_h2_point_evaluation`](../InfiniteZero/ClassicalEllipticSobolev.lean)
and
[`classical_elliptic_interior_estimate`](../InfiniteZero/ClassicalEllipticInterior.lean)
retain their existing statements as proved wrappers.

## Point-evaluation statement

Write \(B_r=B(0,r)\subset\mathbb R^2\), and let \(e_0,e_1\) be the
coordinate unit vectors. The local norm used in the formalization is

\[
 S_n(u;r)^2=\sum_{j=0}^n\ \sum_{\alpha\in\{0,1\}^j}
   \int_{B_r}|D^ju(x)[e_{\alpha_1},\ldots,e_{\alpha_j}]|^2\,dx.
\]

This is [`coordinateSobolevNorm`](../InfiniteZero/EllipticCoordinateNorms.lean).
Order zero is included. All derivatives are real, and function values
may be complex. Ordered derivatives repeat each multi-index with its
multinomial multiplicity.

There exists \(C_S>0\) such that every smooth function
\(u:\mathbb R^2\to\mathbb C\) satisfies

\[
 |u(0)|\le C_S S_2(u;1).
\]

Explicitly, the square of the norm on the right is

\[
 S_2(u;1)^2=\int_{B_1}|u|^2
 +\sum_{i=0}^1\int_{B_1}|\partial_i u|^2
 +\sum_{i,j=0}^1\int_{B_1}|\partial_i\partial_j u|^2.
\]

The constant is independent of \(u\). The function need not vanish on
the boundary of the ball. The Lean predicate is
[`HasH2PointEvaluation`](../InfiniteZero/CoordinateSobolevEmbedding.lean).

## Natural-language proof of point evaluation

First suppose that \(v\) is smooth with compact support contained in
\(B_1\). The function and its derivatives vanish on the lower and left
edges of the rectangle \([-1,0]^2\). Applying the fundamental theorem
of calculus in the two coordinate directions gives

\[
 v(0,0)=\int_{-1}^0\int_{-1}^0
    \partial_1\partial_0v(s,t)\,dt\,ds.
\]

[CoordinateRectangleFTC.lean](../InfiniteZero/CoordinateRectangleFTC.lean)
proves this identity for the actual coordinate derivatives on the
Euclidean plane, including the change to Cartesian product measure.
The rectangle has area one. Cauchy–Schwarz therefore gives

\[
 |v(0)|^2\le\int_{[-1,0]^2}|\partial_1\partial_0v|^2
 \le\int_{B_1}|\partial_1\partial_0v|^2\le S_2(v;1)^2.
\]

The second inequality uses the support of the derivative: its integral
outside \(B_1\) is zero. The Cauchy–Schwarz step for complex-valued
functions is proved in
[UnitMeasureL2Bound.lean](../InfiniteZero/UnitMeasureL2Bound.lean).

For an arbitrary smooth \(u\), choose a fixed smooth cutoff \(\eta\)
equal to one on \(B_{1/2}\), with compact support in \(B_1\), and apply
the preceding result to \(v=\eta u\). The coordinate derivatives of
\(\eta\) through order two have a common finite bound \(B_\eta>0\).
The proved multiplication estimate in
[CoordinateSobolevProduct.lean](../InfiniteZero/CoordinateSobolevProduct.lean)
gives

\[
 |u(0)|=|v(0)|\le S_2(v;1)
 \le K_2B_\eta S_2(u;1).
\]

Thus \(C_S=K_2B_\eta\) is chosen before \(u\).
[CoordinatePointEvaluation.lean](../InfiniteZero/CoordinatePointEvaluation.lean)
assembles these steps. This proves the estimate needed here for smooth
complex functions, without introducing a general theory of weak Sobolev
derivatives or admitting a Sobolev embedding theorem.

For its relation to the usual literature, the estimate is also a
consequence of J. K. Hunter, *Partial Differential Equations*,
[Theorem 3.49(3), p.76](https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf#page=32),
with dimension two, \(k=2\), \(m=0\), and \(p=2\).

## Interior estimates proved in Lean

For every integer \(n\ge0\), \(0<r<R\), and \(B\ge0\), Lean proves
that a constant \(C(n,r,R,B)>0\) exists such that

\[
 S_{n+2}(u;r)\le C(n,r,R,B)
   \bigl(\|u\|_{L^2(B_R)}+S_n(f;R)\bigr)
\]

whenever smooth complex functions satisfy

\[
 -\Delta u+a_0\partial_0u+a_1\partial_1u+qu=f\quad\text{on }B_R,
\]

and every ordered coordinate derivative of \(a_0,a_1,q\) through
order \(n\) has absolute value at most \(B\) on \(B_R\). The constant
is chosen before the coefficients and functions. No boundary
condition or sign condition on the lower-order coefficients is used.

The proof consists of the following steps.

1. [EllipticCaccioppoli.lean](../InfiniteZero/EllipticCaccioppoli.lean)
   constructs a smooth cutoff between two prescribed balls. The
   cutoff energy identity and Young's inequality give a local
   gradient bound using only \(|a_i|,|q|\le B\). Half of the cutoff
   gradient energy is absorbed on the left. Taking real parts
   handles complex lower-order coefficients.
2. [LaplacianHessianEnergy.lean](../InfiniteZero/LaplacianHessianEnergy.lean)
   proves, by two integrations by parts and commutation of mixed
   derivatives, that
   \(\sum_{i,j}\|\partial_i\partial_j v\|_2^2=\|\Delta v\|_2^2\)
   for compactly supported smooth \(v\).
   [LocalPoissonH2.lean](../InfiniteZero/LocalPoissonH2.lean)
   applies this identity to a cutoff of \(u\).
3. [EllipticLocalH2.lean](../InfiniteZero/EllipticLocalH2.lean)
   rewrites the equation to bound \(\Delta u\), and combines the
   preceding estimates on nested balls. This gives the uniform
   local \(H^2\) estimate.
4. [EllipticDifferentiation.lean](../InfiniteZero/EllipticDifferentiation.lean)
   proves the differentiated equation. Its source is
   \(\partial_i f-\sum_j(\partial_i a_j)\partial_j u-(\partial_iq)u\).
   [CoordinateSobolevProduct.lean](../InfiniteZero/CoordinateSobolevProduct.lean)
   and [EllipticSourceSobolev.lean](../InfiniteZero/EllipticSourceSobolev.lean)
   bound this source using Leibniz's rule and the prescribed
   coefficient derivatives.
5. [EllipticSobolevBootstrap.lean](../InfiniteZero/EllipticSobolevBootstrap.lean)
   performs the finite-order induction on nested balls. The
   specialization to \(r=1,R=2\) is assembled in
   [EllipticUniformInterior.lean](../InfiniteZero/EllipticUniformInterior.lean).

These steps use no admitted elliptic or Sobolev result.

## Higher derivatives and norm conversions proved in Lean

[CoordinateSobolevEmbedding.lean](../InfiniteZero/CoordinateSobolevEmbedding.lean)
applies the proved point estimate to each ordered derivative of \(u\). The norm comparison
\(S_2(\partial^\alpha u;1)\le S_{n+2}(u;1)\), for \(|\alpha|\le n\),
is proved in Lean. Thus every coordinate derivative through order
\(n\) at zero is bounded by \(C_S S_{n+2}(u;1)\).

[EllipticCoordinateNorms.lean](../InfiniteZero/EllipticCoordinateNorms.lean)
proves the tensor inequalities

\[
 |T[e_{\alpha_1},\ldots,e_{\alpha_j}]|\le\|T\|,
 \qquad
 \|T\|\le\sum_{\alpha\in\{0,1\}^j}
       |T[e_{\alpha_1},\ldots,e_{\alpha_j}]|.
\]

It also derives \(S_n(f;2)\le\sqrt{N_n}\,F\) from the directional
source bounds, where \(N_n=\sum_{j=0}^n2^j\).
[EllipticSobolevAssembly.lean](../InfiniteZero/EllipticSobolevAssembly.lean)
combines these conversions with the interior estimate and embedding,
proving the public conclusion \(\|D^ju(0)\|\le C(U+F)\) for all
\(j\le n\). The public theorem
[`classical_elliptic_interior_estimate`](../InfiniteZero/ClassicalEllipticInterior.lean)
retains its statement and has no admitted dependency.

## Boundary with the proofs for the particular potential

The change-of-scale identities and its Jacobian are proved without
admitted results in [`AffineScaleJets.lean`](../InfiniteZero/AffineScaleJets.lean)
and [`AffineScaleL2.lean`](../InfiniteZero/AffineScaleL2.lean):

\[
 D_y^j(u(x_0+hy))=h^jD_x^ju(x_0+hy),\qquad
 \int_{B_2}|f(x_0+hy)|^2dy
 =h^{-2}\int_{B(x_0,2h)}|f(x)|^2dx\quad(h>0).
\]

The connections proved separately are the expansion of the actual Hamiltonian in
[`MagneticEllipticExpansion.lean`](../InfiniteZero/MagneticEllipticExpansion.lean),
its equation after rescaling in
[`MagneticAffineRescaling.lean`](../InfiniteZero/MagneticAffineRescaling.lean),
the coefficient bounds on a fixed compact set in
[`RescaledMagneticCoefficientBounds.lean`](../InfiniteZero/RescaledMagneticCoefficientBounds.lean),
and the local comparison of weighted masses in
[`WeightedLocalMassComparison.lean`](../InfiniteZero/WeightedLocalMassComparison.lean).
The exponential weight is compared on the small ball; it remains outside
the estimated derivatives and is not introduced into the elliptic operator.

The detailed physical data for the response and its source are described in
[`ATOMIC_FINE_RESPONSE_DATA.md`](ATOMIC_FINE_RESPONSE_DATA.md).
The generic interior theorem above asserts no estimate of this source,
no action rate, no spectral property of the potential, and no
tunneling asymptotic.

The generic applications are compiled in
[`MagneticInteriorEstimate.lean`](../InfiniteZero/MagneticInteriorEstimate.lean)
and [`WeightedMagneticInteriorEstimate.lean`](../InfiniteZero/WeightedMagneticInteriorEstimate.lean),
with `HasInteriorEllipticEstimate` as an explicit hypothesis. They
derive the loss \(h^{-1}=\lambda\) in dimension two and, for the
inner neighborhood of the cusps, the bound

\[
 e^{\kappa\lambda T(x_0)}h^j\|D^ju(x_0)\|
 \le C\lambda(U+F),\qquad 0\le j\le n.
\]

Here \(U\) bounds the global norm of the weighted solution, and \(F\)
bounds the norms of the weighted semiclassical jets of the source
restricted to the outer neighborhood. The small-scale, center, and
bounded-energy conditions are retained in their statements. These Lean
proofs add no admitted result: their `hInterior` hypothesis is supplied
by the proved public interior theorem.
