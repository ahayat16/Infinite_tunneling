# A002 — Classical realization of the magnetic operator

This document mathematically justifies the exact
[`IsMagneticRealization`](../InfiniteZero/OperatorBridge.lean) contract required
by `magnetic_realization`. The references and their numbering were checked
against the full texts on September 17, 2026. This is a natural-language
proof; the steps described here are not thereby verified in Lean.

**Audit conclusion:** the current assumptions suffice for every field of the
contract. They assume no tunneling result. Two classical analytic inputs
suffice, followed by the deductions detailed below. There is no need to add
`b > 0`, `λ > 0`, compact support for `V`, or a global bound on the derivatives
of `V`.

## References consulted directly

**[S] Mikhail Shubin**, *Essential self-adjointness for semi-bounded magnetic
Schrödinger operators on non-compact manifolds*, arXiv version
`math/0007019v2`, July 30, 2001.
[Version record](https://arxiv.org/abs/math/0007019v2);
[full text](https://arxiv.org/pdf/math/0007019v2).
**Theorem 5.2, p. 10**, gives essential self-adjointness on `C∞_c` on a
complete manifold, for a locally Lipschitz magnetic potential and a locally
bounded electric potential, when the operator is bounded below on `C∞_c`.
The **beginning of §5, p. 10**, specifies the maximal domain through the
differential equation in the distributional sense and identifies it with
the adjoint of the minimal operator. **Lemma 5.1, p. 10**, gives local `H²`
regularity of the maximal domain. The magnetic field conventions appear in
**formulas (2.8)–(2.9), p. 6**. Theorem 1.1, p. 3, also applies, but its
version 5.2 avoids unnecessary assumptions on singular potentials.

**[D] Semyon Dyatlov**, *Lecture notes for 18.155: distributions, elliptic
regularity, and applications to PDEs*, December 10, 2022,
[full text published by the author at MIT](https://math.mit.edu/~dyatlov/18.155/155-notes.pdf).
**Theorem 14.2, p. 181**, establishes equality of the singular supports of
`u` and `Pu` for an elliptic differential operator with smooth coefficients
on a manifold, without a compactness assumption. Its proof appears in
**§14.2.2, p. 194**. **Proposition 8.12, p. 93**, states that an empty
singular support gives a global smooth representative.
This reference is the author's text containing the proofs, not a
second-hand citation or a search-engine summary.

The page numbers refer to the printed pages of the PDFs. The external
results used are exactly those stated above; their applications to our
definitions and the quotient/infimum arguments that follow are made
explicit here.

## Exact assumptions and conventions

Fix `b, λ : ℝ` and `V : Plane → ℝ`, with

\[
 V\in C^\infty(\mathbb R^2),\qquad |V(x)|\le C\quad\text{for every }x.
\]

The constant `C` may be chosen nonnegative: the bound at `x = 0` already
forces `0 ≤ C`. The identification of
`Plane = EuclideanSpace ℝ (Fin 2)` with `ℝ²` uses its canonical orthonormal
basis and its Lebesgue measure. Set

\[
 a(x)=\frac{b\lambda}{2}(-x_2,x_1),\qquad
 D_j=-i\partial_j-a_j(x),\qquad
 H_0=\sum_{j=1}^2D_j^2+\lambda^2V,
 \quad\mathcal D(H_0)=C_c^\infty(\mathbb R^2;\mathbb C).
\]

This is exactly `magneticHamiltonian b λ V` on test functions.
Repeated application of `covariantDerivative` also differentiates the
coefficients occurring in its first application.

**Sign convention to check in [S].** Shubin writes `(D + A)²` with
`D = −i∂`. Thus `A = −a` must be substituted there, and his electric
potential is `λ²V`. There is no sign change in the electric potential.
His inner product is linear in the first factor; the repository's is
linear in the second. Self-adjointness, the norm, and the real part of
diagonal expressions are unchanged by this convention.

The functions `a_j` are real and smooth for all `b, λ`. The potential
`λ²V` is real, smooth, and bounded by `λ²C`. When `b = 0`, this gives a
Schrödinger operator without a field; when `λ = 0`, it gives `−Δ`,
independently of `b` and `V`. No division by `b` or `λ` occurs in the
proof.

## Preliminaries on test functions

If `ψ` is smooth and compactly supported, `D_jψ` and `H₀ψ` are smooth
with support contained in that of `ψ`. Their norms are bounded on this
compact set of finite measure, so they belong to `L²`. The `MemLp`
witnesses required in `magneticTestGraph` exclude no test functions.

Two continuous functions that are equal almost everywhere for Lebesgue
measure are equal everywhere. Indeed, if their difference is nonzero at a
point, its norm is bounded below by a strictly positive constant on a
small open ball, which has positive measure. This contradicts equality
almost everywhere. The map from `C∞_c` into `L²` is therefore injective,
and `H₀` is well defined on these classes.

The test domain is dense in `L²`: truncate an `L²` function to large
balls, then regularize each truncation by convolution with a compactly
supported approximation of the identity. The truncations converge in
`L²`, and the convolutions approximate each truncation in the same norm.
A diagonal choice gives `C∞_c` functions converging to the original
function.

Integration by parts, with no boundary term, gives, for two test functions
`ψ, φ`:

\[
 \langle\psi,H_0\varphi\rangle
 =\sum_j\langle D_j\psi,D_j\varphi\rangle
   +\lambda^2\int\overline\psi V\varphi.
\]

Since the coefficients `a_j` and `V` are real, `H₀` is symmetric. On the
diagonal, the identity gives exactly

\[
 \operatorname{Re}\langle\psi,H_0\psi\rangle
 =q(\psi):=\texttt{magneticForm}\ b\ \lambda\ V\ \psi
 \ge-\lambda^2 C\|\psi\|_2^2.                 \tag{1}
\]

We also have `mass ψ = ‖[ψ]‖₂²`. All these integrals are of integrable
functions: the default value of an integral of a nonintegrable function
is not used.

## The `graph_eq` and `selfAdjoint` fields

Euclidean space is complete, `−a` is locally Lipschitz, `λ²V` is locally
bounded, and (1) provides the required lower bound. All assumptions of
[Shubin's Theorem 5.2](https://arxiv.org/pdf/math/0007019v2#page=10)
are therefore satisfied. The closure `T = closure(H₀)` is self-adjoint.

The test graph is already a complex subspace: the test domain is closed
under addition and scalar multiplication, and the differential expression
is complex-linear on this domain. Taking its `Submodule.span` therefore
does not change its underlying set. By definition of the closure of an
operator, its closure in `L² × L²` is the graph of `T`.
This is precisely `magneticClosedGraph`.

The graph of a linear operator contains no pair `(0,w)` with `w ≠ 0`.
Thus `Submodule.toLinearPMap` reconstructs the operator `T` from its graph
here. The default branch of this Mathlib definition is not used. We obtain
simultaneously

\[
 \texttt{magneticOperator}=T,\qquad
 \operatorname{graph}(\texttt{magneticOperator})
   =\texttt{magneticClosedGraph}.
\]

This proves both fields. The **graph-norm core** property is included:
for each `u ∈ D(T)`, there exist `ψₙ ∈ C∞_c` such that

\[
 [\psi_n]\longrightarrow u,\qquad [H_0\psi_n]\longrightarrow Tu
 \quad\text{in }L^2.                       \tag{2}
\]

This convergence follows from the closure of the graph in a metric space.
There is no need to assume a separate core theorem for a self-adjoint
extension chosen in some other way.

## The `bottom_eq` and `lower_bound` fields

Write `m_test = variationalBottom b λ V` and
`m_op = operatorVariationalBottom T`. These two real infima are taken over
nonempty sets that are bounded below. A nonzero bump function, normalized
in `L²`, provides an element of each set. The bound `−λ²C` holds on test
functions by (1), and on the domain of `T` by (2) and continuity of the
inner product. This explicitly checks the assumptions required for `sInf`
on `ℝ`.

Every normalized test function defines a normalized vector in the domain
of `T`, with the same energy by (1). Hence `m_op ≤ m_test`.

Conversely, let `u ∈ D(T)` have norm one. Choose (2). The norms `‖ψₙ‖₂`
tend to one and are therefore eventually nonzero. Set
`χₙ = ψₙ / ‖ψₙ‖₂` from that index onward. These functions are normalized
test functions, and

\[
 q(\chi_n)
 =\frac{\operatorname{Re}\langle\psi_n,H_0\psi_n\rangle}
        {\|\psi_n\|_2^2}
 \longrightarrow\operatorname{Re}\langle u,Tu\rangle.
\]

Since `m_test ≤ q(χₙ)` at every index, passing to the limit gives
`m_test ≤ Re⟨u,Tu⟩`. Thus `m_test` is a lower bound for the entire set
defining `m_op`, so `m_test ≤ m_op`. This proves `bottom_eq`.

For `lower_bound`, the case `u = 0` is immediate. Otherwise, apply the
preceding inequality to `u / ‖u‖₂ ∈ D(T)`, then multiply by `‖u‖₂²`:

\[
 m_{\rm test}\|u\|_2^2
 \le\operatorname{Re}\langle u,Tu\rangle.
\]

These two proofs use neither an enumeration of the spectrum, nor the
existence of a ground-state eigenvalue, nor the min–max principle for the
second level. They compare exactly the two infima defined in the code.

## The `eigenfunction_iff` field

Fix `E : ℝ`. At the beginning of
[Shubin's §5, p. 10](https://arxiv.org/pdf/math/0007019v2#page=10),
the maximal domain is described by `u ∈ L²` and `Hu ∈ L²` in the
distributional sense. The essential self-adjointness established above
identifies this domain with `D(T)`.

**From operator to classical function.** If `u ∈ operatorEigenspace T E`,
then `u ∈ D(T)` and `Tu = Eu`. Its associated distribution therefore
satisfies `(H − E)u = 0`. This distribution exists because
`L² ⊂ L¹_loc` by Cauchy–Schwarz on compact sets.

The operator `H − E` has smooth complex coefficients and principal symbol
`ξ₁² + ξ₂²`, strictly positive for `ξ ≠ 0`. Apply
[Dyatlov's elliptic regularity theorem, Theorem 14.2](https://math.mit.edu/~dyatlov/18.155/155-notes.pdf#page=181)
to this operator, with zero right-hand side. There exists a function
`ψ ∈ C∞(ℝ²;ℂ)` representing `u` almost everywhere.

This function belongs to `L²` because it represents `u`. The
distributional equation `Hψ − Eψ = 0` is an equation between smooth
functions, so it holds at every point. Thus
`IsEigenfunction b λ V E ψ` and `Represents u ψ` are satisfied.

Regularity must be applied to **`H − E`**, rather than invoking a smooth
right-hand side `Eu` before proving that `u` is smooth. The regularity
required is local; no global bound on the derivatives of `V` is added to
the assumptions.

**From classical function to operator.** Suppose `ψ` is smooth, belongs
to `L²`, satisfies `Hψ = Eψ` everywhere, and satisfies `Represents u ψ`.
Then `Hψ = Eψ ∈ L²` also in the distributional sense. The description of
the maximal domain gives `u ∈ D(T)` and `Tu = Eu`. Membership in
`D(H₀*)` can also be checked directly by integration by parts against
each test function, then using `H₀* = T`.

This direction does not require a prior assumption that all derivatives
of `ψ` belong globally to `L²`. The equation and the maximal domain give
the required membership in the operator domain.

## The `eigenspace_equiv` field

Let `G` be the submodule of functions whose membership condition is
exactly `IsEigenfunction b λ V E`, as required by the field. Define

\[
 J:G\longrightarrow\operatorname{operatorEigenspace}(T,E),
 \qquad J(\psi)=[\psi]_{L^2}.
\]

Each class exists by `MemLp`. The reverse direction of
`eigenfunction_iff` ensures that it belongs to the eigenspace of `T`.
The operations on `L²` classes show that `J` is complex-linear.

If `J(ψ)=0`, then `ψ=0` almost everywhere. Since `ψ` is continuous, the
positive-measure ball argument above implies `ψ=0` everywhere. Thus `J`
is injective. For every vector in the eigenspace of `T`, the forward
direction of `eigenfunction_iff` provides a smooth representative `ψ`;
the exact assumption on `G` gives `ψ ∈ G`. Thus `J` is surjective.

The linear bijection `J` gives the required linear equivalence, and
`Represents (J ψ) ψ` holds by construction. This argument also applies
to the zero space and to an infinite-dimensional eigenspace. Neither
finite multiplicity nor simplicity has been assumed.

## Scope and recommended decomposition

| Current field | Required mathematical input |
|---|---|
| `graph_eq` | Closure of the test graph, absence of a vertical part, reconstruction by `toLinearPMap` |
| `selfAdjoint` | Checked application of Theorem 5.2 of [S] |
| `bottom_eq` | Integration-by-parts identity and graph-norm approximation (2) |
| `lower_bound` | Infimum over normalized vectors, followed by homogeneity |
| `eigenfunction_iff` | Maximal domain from [S], followed by local regularity of `H − E` from [D] |
| `eigenspace_equiv` | Passage to the `L²` quotient, continuity of representatives, and bijectivity |

A002 is therefore a coherent classical package, but broader than a single
imported theorem. A finer Lean decomposition could retain just two
documented classical admissions:

1. **Minimal/maximal realization.** The closed test graph defines a
   self-adjoint operator equal to the maximal distributional operator,
   for the linear magnetic potential and the real, smooth, bounded
   potential.
2. **Regularity of distributional eigensolutions.** Every `L²` vector
   solving `(H − E)u = 0` has the smooth representative described above.

The other fields would then be lemmas to prove in Lean, following the
proofs in this document. Until these lemmas are written, they remain
included in the current admission; this text does not reclassify them as
formal proofs. Such a subdivision also requires a precise Lean interface
for distributions: an informal notion must not be substituted for it in
the type of an axiom.

The main formalization tasks are integration by parts, density of `C∞_c`,
identification of Fréchet derivatives with distributional derivatives,
properties of `Lp.toLp`, and reasoning about infima of nonempty sets that
are bounded below. No missing mathematical assumption has been identified
in the current contract.

However, A002 establishes neither the existence of a ground state, nor
its simplicity, nor a gap, nor a hopping asymptotic, nor the conclusions
of `thm:main`. It also does not identify the second min–max value with
an enumeration of the discrete spectrum. Finally, one must not infer that
**every** vector in the domain is smooth: the smoothness above uses the
homogeneous eigenvalue equation.
