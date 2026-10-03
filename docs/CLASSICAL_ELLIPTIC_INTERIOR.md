# Classical interior elliptic regularity contract

The contract [`HasInteriorEllipticEstimate`](../InfiniteZero/EllipticInteriorContract.lean)
isolates a general local estimate on a fixed ball in dimension two.
This file gives its mathematical justification and exact boundary.
The contract is a proposition definition. The classical input **A005**,
[`classical_elliptic_interior_estimate`](../InfiniteZero/ClassicalEllipticInterior.lean),
asserts precisely this contract with an explicit `sorry`. The informal
proof below documents this admitted result; it is not a Lean proof of
the elliptic estimate.

## Exact statement

Identify `Plane = EuclideanSpace ℝ (Fin 2)` with the Euclidean plane equipped
with Lebesgue measure. All Fréchet derivatives below are real;
the functions and coefficients may be complex. Set

\[
 Lu=-\Delta u+\sum_{i=0}^1 a_i\,\partial_i u+qu,
 \qquad B_2=B(0,2).
\]

For every integer \(n\ge0\) and every bound \(B\ge0\), there exists
\(C=C(n,B)>0\) such that, for **all** coefficients \(a_0,a_1,q\) and
functions \(u,f\), smooth on the plane, the following assumptions imply
the stated conclusion:

- \(Lu=f\) at every point of \(B_2\);
- for \(0\le j\le n\) and \(x\in B_2\),
  \(\|D^j a_i(x)\|\le B\) and \(\|D^j q(x)\|\le B\);
- \(U,F\ge0\), \(\int_{B_2}|u|^2\le U^2\), and, for each
  \(0\le j\le n\) and each family of constant vectors
  \(v_1,\ldots,v_j\) of norm at most one,
  \[
    \int_{B_2}|D^j f(x)[v_1,\ldots,v_j]|^2\,dx\le F^2.
  \]

Then, simultaneously for \(0\le j\le n\),

\[
                   \|D^j u(0)\|\le C(U+F).
\]

The jet norms are the operator norms of the multilinear maps.
Order zero is included: it controls the values of the coefficients and
the \(L^2\) norm of \(f\). The constant precedes the coefficients,
functions, and bounds \(U,F\). No boundary condition, reality of the
coefficients, positivity of \(q\), self-adjointness, or global coercivity
is required. Global smoothness ensures, in particular, integrability over
the bounded ball, but only the equation and bounds in \(B_2\) enter
the estimate.

## Verified primary references

References consulted on September 18, 2026 in John K. Hunter's notes,
*Partial Differential Equations*, UC Davis:

| Result | Location | Use here |
|---|---|---|
| Theorem 4.27 | [Chapter 4, p. 112, PDF page 24](https://www.math.ucdavis.edu/~hunter/pdes/ch4.pdf#page=24) | Interior \(H^2\) estimate for a divergence-form elliptic equation; its specialization to the Laplacian is used. |
| Theorem 4.28 | [Chapter 4, p. 114, PDF page 26](https://www.math.ucdavis.edu/~hunter/pdes/ch4.pdf#page=26) | Higher interior regularity and an \(H^{k+2}\) estimate from a source in \(H^k\). |
| Theorem 3.49(3) | [Chapter 3, p. 76, PDF page 32](https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf#page=32) | Sobolev embedding on a smooth ball; with dimension two, \(p=2\), \(k=n+2\), \(m=n\), it controls the \(C^n\) norm. |

The complex contract with lower-order terms is an **adapted consequence**,
not the literal statement of any one of these theorems. In particular,
the regularity of the variable principal coefficients in Hunter's results
is not an additional assumption here: the principal part is exactly
\(-\Delta\), with constant coefficients.

## Proof of the adapted version

Choose a finite number of nested concentric balls between \(B_2\)
and \(B_1\), together with associated smooth cutoffs. Their choice depends
only on \(n\).

**Complex energy estimate.** Multiply the equation by
\(\chi^2\overline u\), integrate, and then take the real part. The
principal term gives \(\int\chi^2|\nabla u|^2\). The other terms are
bounded using \(|a_i|,|q|\le B\), the source, and the derivatives of
\(\chi\). Young's inequality absorbs the terms containing
\(\chi|\nabla u|\) and gives

\[
 \|u\|_{H^1(B_{r_1})}\le C_1(B)(U+F),\qquad r_1<2.
\]

Taking the real part is essential; no sign of the complex coefficient
\(q\) is used. Keeping \(\|u\|_{L^2}\) on the right-hand side removes
the need for a coercivity assumption.

**Gain of two derivatives for Poisson.** Write
\(-\Delta u=f-a\cdot\nabla u-qu\). The right-hand side is controlled
in \(L^2(B_{r_1})\) by the previous step. The interior Poisson estimate,
applied to the real and imaginary parts, gives an \(H^2\) bound on
a strictly smaller ball.

**Commutation and induction.** For a multi-index \(\alpha\) of
length \(k\le n\), differentiate the Poisson identity:

\[
 -\Delta\partial^\alpha u
 =\partial^\alpha f
  -\partial^\alpha(a\cdot\nabla u)-\partial^\alpha(qu).
\]

Leibniz's rule involves only derivatives of \(a,q\) of order at most
\(k\), and of \(u\) of order at most \(k+1\).
The latter are controlled at the previous stage on the outer ball
for the current step. The Poisson estimate then gives control of order
\(k+2\) on the inner ball. The induction yields

\[
 \|u\|_{H^{n+2}(B_1)}
 \le C_2(n,B)\bigl(\|u\|_{L^2(B_2)}+\|f\|_{H^n(B_2)}\bigr).
\]

This explains why **coefficient jets through order \(n\) suffice**,
including for \(n=0\). No variable principal coefficient is differentiated.

**Norm conversion and pointwise evaluation.** The assumptions for all
unit directions include tuples of vectors from the orthonormal basis.
They therefore give
\(\|f\|_{H^n(B_2)}\le c_nF\), by a finite sum of coordinate
derivatives. In dimension two, the embedding
\(H^{n+2}(B_1)\hookrightarrow C^{n,1/2}(\overline{B_1})\)
controls the coordinate derivatives of \(u\) at zero. Equivalence
of norms on finite-dimensional tensors then controls their operator
norm. All these factors depend only on \(n\), and are absorbed
into \(C(n,B)>0\).

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
The classical contract above asserts no estimate of this source,
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
proofs add no admitted result: A005 is used only when its theorem is
supplied to their `hInterior` hypothesis.
