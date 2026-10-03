# Potential construction: proved results

All results cited here are proved without `sorry` and without dependencies on admissions. Their transitive status is checked in the [inventory](STATUS.md).

## Assumptions and existence

`CuspParameters.BasicConditions` states the elementary constraints: positivity of the parameters, `8r₀ < R`, `εa < 1/4`, `√3 s₀ t₀ ≤ 1/2`, regularity and localization of both cutoffs, their bounds in `[0,1]`, their plateaus, and evenness of the tangential cutoff.

These conditions have a concrete witness in `ConstructionParameters.lean`: `r₀=1`, `R=16`, `b=1`, `ε=1/16`, `a=β=tStar=s₀=1`, `t₀=1/100`. The cutoffs use Mathlib’s `ContDiffBump` functions. `ConstructionExistence.lean` deduces an explicit admissible potential.

This witness does **not** certify every small constant in the article’s analytic hierarchy. At this construction milestone, existence of parameters also satisfying the source, saddle, and spectral-transfer estimates remained open problem O001; that existence was no longer admitted through a global lemma.

## Regularity across the tip

The radial core is rewritten using Mathlib’s smooth function `expNegInvGlue`; this identity also handles the boundary `‖x‖=r₀`.

The cusp smoothness proof uses a family closed under differentiation. For a natural number `k` and real polynomial `P`, it defines

\[
F_{k,P}(t)=t^{-k}P(\log(t_*/t))
e^{-\beta\log^2(t_*/t)}\quad(t>0),\qquad F_{k,P}(t)=0\quad(t\le0).
\]

`LogFlat.lean` proves decay after multiplication by any inverse power and any logarithmic power. `LogFlatSmooth.lean` proves the recurrence on the whole real line

\[
F'_{k,P}=F_{k+1,(2\beta X-k)P-P'}.
\]

The derivative at zero is justified by difference quotients, rather than merely computed formally for `t>0`. Induction gives smoothness and vanishing of every derivative at zero; each derivative decays faster than every power.

`CuspKernelSmooth.lean` then treats

\[
K_{k,P,g}(t,u)=F_{k,P}(t)g(u/t^2),\qquad g\in C_c^\infty(\mathbb R).
\]

On `t=0`, an `o(‖(t,u)-(0,u₀)‖)` estimate proves Fréchet differentiability with zero derivative. Away from this line, the usual calculation gives

\[
\partial_tK=K_{k+1,(2\beta X-k)P-P',g}
             -2uK_{k+3,P,g'},\qquad
\partial_uK=K_{k+2,P,g'}.
\]

These formulas also hold on the line, and the family is closed under this operation. Induction on the regularity order therefore proves `ContDiff ℝ ∞` on the whole coordinate plane.

Finally, `ConstructionCuspFormula.lean` proves that chart-domain indicators are redundant because of the cutoff supports. `ConstructionSmooth.lean` composes the kernel with affine coordinates, multiplies by the normal cutoff, and adds the core and reflected cusp. The result `admissiblePotential` has no cusp-smoothness assumption.

`ConstructionCuspJets.lean` further proves that **all iterated Fréchet derivatives** of both cusps vanish at their tips. The proof uses their vanishing on the exterior half-plane and continuity of every derivative up to the boundary. It includes order zero.

This proof directly targets the regularity required by `thm:main`. It does not yet provide the blueprint’s quantitative common bound `C_m t^{-N_m}(1+ℓ)^{N_m}e^{-βℓ²}` for all Cartesian jets.

## Cusp chart, Jacobian, and weighted integral

[`CuspChartJacobian.lean`](../InfiniteZero/CuspChartJacobian.lean) defines the chart in the real Euclidean plane

\[
\Psi_p(t,s)=p.\mathrm{cuspTip}+t\,n+s t^2\,\tau,
\qquad t>0,
\]

where `n = cuspNormal` and `τ = cuspTangent` form the cusp’s orthonormal frame. The normal and tangential coordinates of this image are `t` and `s t²`, respectively. The file proves injectivity on `t>0`, smoothness, the explicit inverse, and

\[
\left|\det D\Psi_p(t,s)\right|=t^2.
\]

The identification of `Plane` with Cartesian coordinates preserves Lebesgue measure. The theorem `integral_image_cuspChart` therefore applies Mathlib’s actual change-of-variables theorem, with normalization `dx = t² dt ds`. The nonzero support of `p.cuspPlus` lies in the image of the rectangle `(0,t₀) × (−s₀,s₀)`; `integral_cuspPlus_smul_rectangle` thus reduces every integral against this component to the rectangle.

Under `p.BasicConditions`, set `w₊ = p.cuspPlus`, `a = p.a`, and `t(x) = p.normalCoordinate x`. For a normal slope `α`, the theorem `integral_abs_cuspPlus_mul_exp` gives the exact identity

\[
\int_{\mathbb R^2}|w_+(x)|e^{-\alpha t(x)/h}\,dx
=a\left(\int_{-s_0}^{s_0}\chi_b(s)\,ds\right)
  \int_0^{t_0}\chi_a(t)t^2
  e^{-\beta\log^2(t_*/t)-\alpha t/h}\,dt.
\]

The Lean integrals are over the indicated open intervals. The normal power is exactly **`m=2`**, from the Jacobian; the outer factor is exactly **`p.a * (∫ χb)`**. The potential is defined as `p.core + p.ε * (p.cuspPlus + p.cuspMinus)`: `ε` is external to `w₊` and therefore absent from this identity. An integral involving the component `ε w₊` receives an additional factor `ε`, positive under `BasicConditions`.

Combining this identity with `LogFlatIntegral.lean`, `eventually_integral_abs_cuspPlus_mul_exp_le` proves, for each `αMin>0` and loss `η>0`, uniformly in `α≥αMin` as `h→0+`,

\[
\int_{\mathbb R^2}|w_+(x)|e^{-\alpha t(x)/h}\,dx
\le a\left(\int_{-s_0}^{s_0}\chi_b(s)\,ds\right)
e^{-(\beta-\eta)\log^2(1/h)}.
\]

This result estimates the **geometric profile of the potential** with an explicit normal weight. The atomic source also contains the atomic eigenstate and a factor `h⁻²`; its estimates and asymptotics do not follow from this identity alone. No estimate on this eigenstate is a hidden assumption of `CuspChartJacobian.lean`.

## Complex charts and active window

`ComplexCuspGeometry` extends the polynomial charts to two complex coordinates. The radius uses the bilinear sum of squares and its principal square root; it agrees with the Euclidean radius at real points. The two source radii and bridge radius are `R,R,2L−R` at the tips. The normal derivatives of both source radii and both derivatives of the bridge radius are `1/2`. A common analytic bidisk works for every tangential parameter in `[-s₀,s₀]`.

`ComplexCuspRemainder` then proves, with `D=2L−R>0`, the existence of a common bidisk and constant `C>0` such that

\[
\begin{aligned}
 |r_+(t,s)-R-t/2|&\le C|t|^2,\\
 |r_-(u,r)-R-u/2|&\le C|u|^2,\\
 |r_{\mathrm{pont}}(t,u,s,r)-D-(t+u)/2|
   &\le C(|t|^2+|u|^2),
\end{aligned}
\]

uniformly for `|s|,|r|≤s₀`. The proof factors the difference of squares and uses the nonnegative real part of the principal square root. Constants are explicit; no Hessian bound is admitted. The sum of these three remainders divided by `h` tends uniformly to zero on `|t|,|u|≤tStar h^(3/4)`. Passing from radii to the total action and amplitudes is a separate step.

`CuspActiveWindow` proves that, for the potential parameters already fixed and `R<2L`, the window `T_h=tStar h^(3/4)` lies in this bidisk for all sufficiently small `h>0`. The actual cutoff `p.χa` equals `1` on `[0,T_h]`. This allows work with the local formula without assuming that the cutoff itself is holomorphic. Atomic-amplitude control remains a separate obligation.

## Other construction properties

- `ConstructionCompact.lean` proves compact support by frame reconstruction and norm control.
- `ConstructionSupportSeparation.lean` separates the **closed supports** of the core, upper cusp, and lower cusp. The width condition places the upper cusp above its tip, and reflection places the other below.
- `Construction.lean` proves the `[-1,0]` bound and reflection symmetry.
- `ConstructionNonradial.lean` exhibits two points of equal norm where the potential values differ.
- `ConstructionMinimum.lean` proves `v(0)=-1`, `v(x)>-1` for `x≠0`, local agreement with the core, and differentiability with zero derivative. It also computes, for every direction `u`,
  \[
  \frac{d^2}{dt^2}v(tu)\big|_{t=0}=\frac{2\|u\|^2}{r_0^2}.
  \]
  This is strictly positive for `u≠0`. The Lean declaration is a second directional derivative; it does not use a separately defined Hessian matrix.
