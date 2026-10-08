# Complex saddle: verified results and scope

The saddle work proves analytic calculations without admitting Lambert W or the steepest-descent method. It remains separate from estimates on the atomic state and the full active cell.

## Branch construction

`ComplexLambertRoot` constructs by contraction a solution of `w + Log w = L`, with `Re w ≥ 2`. The iteration is `w ↦ L − Log w` on a disc centered at L. This disc is larger than in the manuscript, but the exact equation subsequently gives the fine estimate `|w − (L − Log L)| ≤ R/(Re L − R)`.

`ComplexLambertAsymptotics` establishes, uniformly for `|d| ≤ M`,

\[
 w(\ell+d)=\ell-\log\ell+d+o(1),\qquad
 \Re w\ge\ell/2,\qquad |\Im w|\le M+\pi.
\]

The error is explicitly bounded by `(8 log ℓ + 2M)/ℓ`. `ComplexLambertRegularity` proves holomorphy on the open domain of strict contraction inequalities, derivative `w/(1+w)` with respect to L, and derivative `w/[c(1+w)]` after composition with `d+Log(Ac)`. These properties are not hypotheses about a special function.

## Connection to the actual integral coefficient

`ComplexLogFlatSaddle` takes exactly

\[
 L=\log(1/h)+\Log\frac{ct_*}{2\beta}+\frac{k+1}{2\beta},\quad
 f(y)=\beta y^2+\frac{ct_*}{h}e^{-y}+(k+1)y.
\]

For fixed parameters `β>0`, `t*>0`, and `c≠0`, the following identities are proved for every sufficiently small `h>0`, without assuming a critical point:

\[
 y_c=w-\frac{k+1}{2\beta},\quad f'(y_c)=0,\quad
 f(y_c)=\beta(w^2+2w)-\frac{(k+1)^2}{4\beta},\quad
 f''(y_c)=2\beta(1+w),\quad
 t_c=t_*e^{-y_c}=\frac{2\beta h}{c}w=O(h\log(1/h)).
\]

`ComplexSaddleBranches` takes imaginary parts of the equation involving Log, not merely its exponential: `Im w + arg w = arg c`. For `Re c>0`, the angle along the vertical connector stays in the right half-plane, and `Re(c exp(−iη)) ≥ Re c` for every η between 0 and Im w.

## Actual integrals

`ComplexLogFlatChange` proves the Lebesgue change of variables `t=t* exp(−y)` in the integral over `(0,t₂)`. The factor is exactly `t*^(m+1)` and the linear phase term is m+1, for `m : ℕ`; the physical Jacobian case m=2 is included. Integrability on both sides is also proved.

`ComplexLogFlatContour` proves equality between the real ray, vertical connecting segment, and shifted ray. The proof applies Cauchy's theorem on a finite rectangle, then sends its right side to infinity with a Gaussian bound.

On the full line through the saddle, `ComplexLogFlatPhase` gives the exact identity

\[
 f(y_c+q)-f(y_c)=\beta q^2+2\beta w(e^{-q}-1+q).
\]

`ExponentialRemainderBounds` proves `e^(−q)−1+q ≥ e^(−1) min(q²,|q|)/2`, then its dilated version. By dominated convergence, `ComplexSaddleLeading` deduces the complex limit

\[
 \sqrt{\Re w}\int_{\mathbb R}
 e^{-\beta q^2-2\beta w(e^{-q}-1+q)}\,dq
 \longrightarrow \sqrt{\pi/\beta}
\]

whenever `Re w→∞` and Im w stays bounded. The leading term is nonzero. `ComplexLogFlatLeading` applies this limit to the actually constructed root.

`ComplexLogFlatErrors` bounds the vertical segment and left tail by `C exp(−d/h)`, with `d=t* exp(−y₂) Re c>0`. `ComplexLogFlatNormalization` proves these errors remain negligible after multiplication by `sqrt(Re w) exp(f(yc))`. The assembly `ComplexLogFlatAsymptotic` therefore establishes, for the **original** integral at fixed parameters and `Re c>0`,

\[
 \sqrt{\Re w}\,e^{f(y_c)}
 \int_0^{t_2} t^m e^{-\beta\log^2(t_*/t)-ct/h}\,dt
 \longrightarrow t_*^{m+1}\sqrt{\pi/\beta}\ne0.
\]

In particular, this complex integral is nonzero for sufficiently small h. The change of variables, measures, integrability, contour, and smallness of the errors are all part of the Lean proof.

`ComplexLogFlatCutoff` then establishes an exponential cutoff-error bound. `ComplexLogFlatCutoffAsymptotic` deduces the **same limit** for `∫₀ᵗ⁰ χa(t) t^m exp(−β log²(t*/t)−ct/h) dt`. The theorem `CuspParameters.tendsto_normalCutoffIntegral_normalized` checks these hypotheses for **the constructed potential's function `p.χa`**, from `p.BasicConditions`. Eventual nonvanishing of this cutoff integral is also proved. Here m=2 corresponds to the cusp Jacobian; atomic source factors are not included.

The result is a limit with relative `o(1)` error. It claims neither the `O(1/|w|)` rate, differentiated expansions, nor all the manuscript's uniformity. The final oscillation goal only requires a relative error tending to zero. Application to the full active integrand separately justifies its uniformity and amplitude control in the [physical assembly](INCOMING_PHYSICAL_ASYMPTOTIC.md).

## Phase and absolute control

`ComplexLogFlatPhaseGrowth` defines the real phase of the leading term by `θ(h)=−Im f(yc)`. The constructed branch is continuous for all large `λ=1/h`, and `θ(1/λ)/λ→0`. The proof uses actual holomorphy of the root and `|f(yc)|=O(log²(1/h))`. Decomposition of the leading term into a strictly positive real size and exp(iθ) is exact. This is the phase of the model normal integral; the [channel assembly](ACTIVE_CHANNEL_ASYMPTOTIC.md) now combines it with the magnetic phase to obtain a continuous total phase of linear growth.

`ComplexSaddleAbsolute` strengthens complex convergence to absolute control usable for multiplicative errors. If `Re w≥1`,

\[
 \sqrt{\Re w}\int_{\mathbb R}
 \left|e^{-\beta q^2-2\beta w(e^{-q}-1+q)}\right|\,dq\le C_\beta.
\]

The constant is independent of Im w. After multiplication by the norm of the actual normalizer `N(h)=sqrt(Re w) exp(f(yc))`, the same bound holds for the absolute integral on the saddle line in the original coordinates. Thus a uniform multiplicative error of size ε costs at most Cβε in the normalized integral. A restricted-measure lemma is proved for a measure on an arbitrary space. `ComplexSaddleProduct` deduces control on the **product of both saddle contours**, including after restriction to any set: the constant is Cβ², and the threshold is independent of the set. Bounds and integrability of the physical multiplier are supplied in [CuspSaddleMultiplier](../InfiniteZero/CuspSaddleMultiplier.lean) and [AtomicCuspDoubleRayShift](../InfiniteZero/AtomicCuspDoubleRayShift.lean). For a multiplier controlled only near the tips, restriction to the truncated contour is essential.

## Moving normal window

`LogFlatActiveWindow` takes

\[
 T_h=t_*h^{3/4},\qquad a_h=\tfrac34\log(1/h).
\]

Lean verifies `|tc|/T_h→0`, `T_h→0`, and `T_h²/h→0`. `LogFlatActiveTruncation` makes the contour-estimate threshold independent of the real endpoint a, then applies it at a=a_h. The sum of the vertical connector and left tail is bounded by

\[
 C\exp\bigl(-t_*\Re(c)h^{-1/4}\bigr).
\]

`LogFlatStretchedErrors` proves that N(h) absorbs this error: h^(−1/4) dominates every power of log(1/h). This gives the **same nonzero limit** for the normal integral over `(0,T_h)`. On the shifted ray x≥a_h and the vertical connector, the complex normal point `t=t* exp(−x−iη)` satisfies `|t|≤T_h`.

`LogFlatActiveRealTail` also controls the **real** normal tail on `[T_h,t₀)`: for any slope `A≥A₀>0`, it is bounded by `t₀^(m+1) exp(−A₀ tStar h^(−1/4))`. Smallness after multiplication by the norm of a reference complex normalizer is uniform over `A∈[A₀,∞)`. The real coefficient may therefore vary with h under this lower bound alone. `LogFlatPolynomialErrors` also absorbs any factor h^(−N), for natural N, even after multiplication by **two** complex normalizers.

This window, wider than `O(h log(1/h))`, suffices for relative `o(1)` error when the actual phase remainders are `O((|t|²+|u|²)/h)` and amplitudes are uniformly close to their tip values. **These active-cell estimates do not follow from model truncation.** Analyticity of the three radii on a common bidisc is established in `ComplexCuspGeometry`. `ComplexCuspRemainder` proves the three quadratic remainders of the **chart radii**, uniformly in tangential variables; divided by h, they are negligible on the window. `ComplexCuspKernelProfile` uses them to connect the three actual kernels to their linear profiles, as detailed below. Atomic amplitudes require separate analysis. `CuspActiveWindow` checks that the entire window lies in this common domain and that the actual cutoff p.χa equals 1 there on the real axis. No analyticity of the smooth cutoff is postulated.

The [natural-language proof for the complex kernel on this window](SHRINKING_COMPLEX_KERNEL_PLAN.md) describes an assembly now proved in Lean that avoids an all-orders complex expansion: the radial displacement O(h^(3/4)) is small compared with the proper-time Gaussian scale sqrt(h). `ComplexLandauAsymptotic` proves the relative term `1+o(1)` of the actual kernel, uniformly on this window and positive compact sets of real energy and radius. Local domination, tails, and exact decomposition are included in the proof.

`ComplexLandauHolomorphic` now proves holomorphy of the **actual kernel defined by the proper-time integral**, for fixed b,h,E>0, on Re(z²)>0. Differentiation under the integral uses an integrable real majorant on a complex neighborhood and a Cauchy derivative estimate. This does not give a uniform differentiated asymptotic expansion to all orders.

`ComplexCuspKernelHolomorphic` composes this kernel with the three complex chart radii. All three compositions and their product are jointly holomorphic in `(t,u)` on the common geometric domain. For R>0, 2L>R, and bounded tangential variables, a fixed bidisc works simultaneously for all b,h>0 and three independent positive real energies. This is uniformity of the **holomorphy domain**, without an additional assertion of derivative bounds as h→0.

For the charts z₊(t,s) and z₋(u,r), `ComplexCuspKernelProfile` proves the following three relative limits, with `D=2L−R>0`:

\[
\begin{aligned}
\frac{h^{3/2}e^{(J_E(R)+J'_E(R)t/2)/h}
 K_h^E(\operatorname{rad}z_+(t,s))}{k_0(E,R)}&\longrightarrow1,\\
\frac{h^{3/2}e^{(J_E(R)+J'_E(R)u/2)/h}
 K_h^E(\operatorname{rad}z_-(u,r))}{k_0(E,R)}&\longrightarrow1,\\
\frac{h^{3/2}e^{(J_E(D)+J'_E(D)(t+u)/2)/h}
 K_h^E(\operatorname{rad}\operatorname{bridge}(z_+,z_-))}{k_0(E,D)}
 &\longrightarrow1.
\end{aligned}
\]

Here rad is the constructed complex square root, not the Hermitian norm. The results accept arbitrary moving parameters with E→E₀>0, |t|,|u|≤M T_h, and eventually |s|,|r|≤s₀; tangential variables need not converge. The parameters b,R,L,tStar,s₀,M remain fixed. No energy convergence rate is imposed, since the action and coefficient use the actual moving energy. Each application may use its own positive real energy. The theorems are limits with moving parameters; no new compact-uniform formulation of these compositions is claimed here.

`ComplexCuspPhase` also handles the **actual magnetic factor**. The polynomial extension of `Geometry.phase` satisfies exactly

\[
\Phi_{\mathbb C}(z_+(t,s),z_-(u,r))
 =\Phi_*+\theta(t+u)+\mathcal R_\Phi,\qquad
\theta=\sqrt3\,bL/2,
\]

with an explicitly computed polynomial remainder and a bound `|RΦ|≤C(|t|²+|u|²)` on |t|,|u|≤1, uniform for bounded tangential variables. Hence exp(i RΦ/h)→1 on the active window, without assuming a remainder.

The source estimates and [four-variable physical asymptotic](INCOMING_PHYSICAL_ASYMPTOTIC.md) are now proved: source factors, deformation of the full integrand, and integrated errors are justified separately. These conclusions do not follow from kernel profiles and geometric phase alone. They feed into the [canonical channels](ACTIVE_CHANNEL_ASYMPTOTIC.md), then the [final proof](../InfiniteZero/Remaining.lean), modulo A002 and A004.
