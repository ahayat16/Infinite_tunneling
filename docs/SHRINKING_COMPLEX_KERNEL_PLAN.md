**Complex kernel on the active window: proposition and natural-language proof**

Audit of September 17, 2026, updated after formalization. **The complex proposition below is now proved without admissions** in [ComplexLandauAsymptotic.lean](../InfiniteZero/ComplexLandauAsymptotic.lean). Holomorphy of the integral is also proved separately in `ComplexLandauHolomorphic`. Differentiated asymptotic expansions on fixed complex neighborhoods remain outside these results.

The proposed simplification is valid. For an `O(h^(3/4))` radial perturbation, the relative leading term of the kernel can be proved while keeping proper time real, without a complex Morse lemma or deformation of that contour. It replaces only the order-zero assertion needed on this window. It does not prove every assertion of [`thm:complex-kernel`, TeX lines 4505–4526](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L4505).

**Exact formalized proposition.** Fix `b > 0`, `tStar > 0`, `M ≥ 0`, and two compact real intervals

\[
K_E=[E_-,E_+]\Subset(0,\infty),\qquad
K_r=[r_-,r_+]\Subset(0,\infty).
\]

For `h > 0`, `E ∈ K_E`, and `Re(z²) > 0`, define the radial extension by the same integral as the real kernel:

\[
\begin{aligned}
q(\tau)&=\frac b4\coth(b\tau),&
a(\tau)&=\frac{b}{4\pi\sinh(b\tau)},\\
H_E(\tau;r)&=E\tau+q(\tau)r^2,&
\mathcal K_h(E,z)&=h^{-2}\int_0^\infty
a(\tau)\exp\!\left[-\frac{E\tau+q(\tau)z^2}{h}\right]d\tau.
\end{aligned}
\]

This convention includes the factor `b/(4π)` in `a`. It agrees with [`landauKernel`](../InfiniteZero/LandauKernel.lean#L23) at positive real radii. Set

\[
\begin{aligned}
s=s(E,r)&=\operatorname{bridgeTime}(b,E,r),\\
J(E,r)&=H_E(s;r)=\operatorname{bridgeAction}(b,E,r),\\
j(E,r)&=\partial_rJ(E,r)=2r q(s)
 =\sqrt{E+b^2r^2/4},\\
D(E,r)&=\partial_\tau^2H_E(s;r)>0,\\
k_0(E,r)&=a(s)\sqrt{2\pi/D(E,r)}>0.
\end{aligned}
\]

The coefficient `k₀` is exactly [`landauLeadingCoefficient`](../InfiniteZero/LandauLaplaceLeading.lean#L265). With `T_h = tStar * h^(3/4)`, we have

\[
\boxed{\quad
\sup_{\substack{E\in K_E,\ r\in K_r\\|\delta|\le M T_h}}
\left|
\frac{\mathcal K_h(E,r+\delta)}
 {h^{-3/2} k_0(E,r)
  \exp[-(J(E,r)+j(E,r)\delta)/h]}-1
\right|\longrightarrow0\quad(h\downarrow0).
\quad}
\]

For sufficiently small h, all arguments satisfy `Re((r+δ)²)>0`. The denominator is nonzero. A Lean formulation with a fixed parameter domain can write `δ = T_h * ξ`, `ξ ∈ closedBall 0 M`, and use `TendstoUniformlyOn` on `K_E × K_r × closedBall 0 M`.

The requested version with fixed radius `r₀` and real energy `E_h → E₀ > 0` is a special case. **The rate `E_h-E₀=O(h)` is unnecessary** if `J`, `j`, and `k₀` are evaluated at `E_h` as above. No fact about the atomic energy is included in this proposition.

**Detailed natural-language proof.**

1. **Convergence and uniform real parameters.** On the enlarged compact sets used below, the minimizers `s(E,r)` remain in an interval `[s_-,s_+] ⊂ (0,∞)`. Choose a fixed `ε ∈ (0,s_-/4)`. On every interval `|τ-s(E,r)|≤ε`, the amplitude a, coefficient q, and their required derivatives are uniformly bounded; also `∂²_τ H_E ≥ m > 0`. Constants depend on neither h nor δ. The complex integral is absolutely convergent: near zero its modulus is at most `C τ⁻¹ exp(-c/(hτ))`; at infinity it is at most `C exp(-bτ) exp(-E_- τ/h)`. For fixed h, the same majorants, with extra powers of `1/τ` if needed, justify differentiation in z under the integral on compact subsets of `Re(z²)>0`. This also gives the radial holomorphy needed for a later spatial contour deformation, without complex Morse theory.
   **Lean scope:** convergence and the norm identity are proved. `ComplexLandauHolomorphic` also justifies differentiation under the integral: a local integrable real majorant controls the integrand, then a Cauchy estimate controls its derivative. For fixed `b,h,E>0`, the kernel is `AnalyticOnNhd` on `Re(z²)>0`. This holomorphy is separate from the asymptotic proof below, which keeps proper time real.

2. **Exact extraction of the linear term.** For `z=r+δ`, the identity

   \[
   E\tau+q(\tau)z^2-J(E,r)-j(E,r)\delta
   =H_E(\tau;r)-J(E,r)
    +2r\delta\,[q(\tau)-q(s)]+\delta^2q(\tau)
   \tag{1}
   \]

   is purely algebraic. It eliminates the potentially large term `δ/h`. One must not bound `exp(-jδ/h)` by a constant or directly replace `exp(-q(τ)(2rδ+δ²)/h)` by `1`.

3. **Local Gaussian limit.** In `|τ-s|<ε`, write `τ=s+√h x`. The exact change of variables turns the local contribution to `h^(3/2) exp((J+jδ)/h) K` into

   \[
   \int_{|x|<\varepsilon/\sqrt h} a(s+\sqrt h x)
   \exp\!\left[-\frac{H_E(s+\sqrt h x;r)-J}{h}
   -\frac{2r\delta[q(s+\sqrt h x)-q(s)]
              +\delta^2q(s+\sqrt h x)}h\right]dx.
   \tag{2}
   \]

   For x in a bounded interval, the second phase term is uniformly `O(|δ|/√h * |x| + |δ|²/h)`, hence `O(h^(1/4)|x| + h^(1/2))`. The first converges uniformly to `D(E,r)x²/2`. This follows from second-order Taylor expansion and uniform continuity of `∂²_τ H` on a real compact set; no expansion to all orders is required. The limiting integrand is `a(s) exp(-D(E,r)x²/2)`.

4. **Actual domination throughout the local region.** Set `L = 2 r_+ sup|q'|` and `Q = sup|q|` on the common real interval. Taylor expansion and (1) give, with `u=τ-s`,

   \[
   \begin{aligned}
   \Re(E\tau+q(\tau)z^2-J-j\delta)
   &\ge \frac m2 u^2-L|\delta||u|-Q|\delta|^2\\
   &\ge \frac m4 u^2-C|\delta|^2,
   \qquad C=Q+L^2/m.
   \end{aligned}
   \tag{3}
   \]

   The modulus of the integrand in (2) is therefore bounded by `a_max exp(C|δ|²/h) exp(-m x²/4)`. Since `|δ|²/h ≤ M² tStar² h^(1/2) → 0`, a fixed multiple of this Gaussian is a common integrable majorant. To obtain **uniform** convergence of the integrals, truncate at `|x|≤R`, use uniform convergence on that compact set, then make both Gaussian tails uniformly small by choosing R large. This avoids incorrectly deducing uniform convergence from a merely pointwise dominated-convergence argument. The limiting integral is `k₀(E,r)`.

5. **All proper-time tails, including zero and infinity.** The local bound on q cannot be extended to `τ=0`, where q diverges. Write `δ=u+iv` and introduce the auxiliary real radius

   \[
   \rho=\sqrt{\Re((r+\delta)^2)}
        =\sqrt{(r+u)^2-v^2}.
   \]

   Once `|δ|≤min(r_-/4,1)`, this radius remains in an enlarged positive compact interval, for example `[r_-/2,r_++1]`. Exactly,

   \[
   \left|a(\tau)e^{-(E\tau+q(\tau)(r+\delta)^2)/h}\right|
       =a(\tau)e^{-H_E(\tau;\rho)/h},\qquad \tau>0.
   \tag{4}
   \]

   Moreover,

   \[
   \rho-r-u=\frac{-v^2}{\rho+r+u},\qquad
   |\rho-r-u|\le C|\delta|^2,\quad |\rho-r|\le C|\delta|.
   \]

   Since the real derivatives `∂_r J` and `∂²_r J` are bounded on the enlarged compact set, real Taylor expansion gives the decisive uniform comparison

   \[
   |J(E,\rho)-J(E,r)-j(E,r)\Re\delta|\le C|\delta|^2.
   \tag{5}
   \]

   Uniform continuity of `s(E,r)` ensures `|s(E,ρ)-s(E,r)|<ε/2` for sufficiently small h. Thus `|τ-s(E,r)|≥ε` implies `|τ-s(E,ρ)|≥ε/2`. By positivity of the real integrand, (4) bounds the entire complex tail by `landauTailKernel b h E ρ (ε/2)`. The already proved uniform real bound gives

   \[
   e^{J(E,\rho)/h}K^{\rm tail}_{h,E}(\rho)
        \le C_1 e^{-d/h},\qquad d>0.
   \]

   After complex normalization, (5) bounds the tail modulus by `C₁ h^(3/2) exp(C|δ|²/h) exp(-d/h)`, which tends uniformly to zero. This handles very small times, intermediate noncritical times, and large times simultaneously. Proper time is never moved into the complex plane.

6. **Relative assembly.** Add (2) and the tail. The result is `h^(3/2) exp((J+jδ)/h) K → k₀(E,r)` uniformly. The coefficient k₀ is continuous and strictly positive on `K_E×K_r`, hence has a uniform positive lower bound. Dividing by k₀ proves the proposition.

**Concrete reuse and limitations.**

- The small-perturbation criterion is actually `sup|δ|/√h → 0`. The same proof covers `|δ|≤C h^α` for any `α>1/2`. At scale `δ=O(√h)`, the extra terms in (2) no longer vanish, and the linearized formula with ratio tending to `1` generally fails: already for real `δ=a√h`, the limiting ratio is `exp(-a² ∂²_rJ(E,r)/2)`.
- For a complex vector argument `x+η`, with `|x|` in a positive real annulus and `|η|=O(T_h)`, choose the branch of `((x+η)·(x+η))^(1/2)` that is positive on the real locus. It satisfies `δ = (x/|x|)·η + O(|η|²)` uniformly. The additional exponent error is `O(T_h²/h)=o(1)`. Constructing this branch and the general algebraic estimate remains a separate formalization task. For the specific cusp charts, the common bidisc and quadratic remainders are already proved in `ComplexCuspGeometry` and `ComplexCuspRemainder`. `ComplexCuspKernelProfile` deduces relative profiles for the two source kernels and bridge kernel, with respective linear displacements `t/2`, `u/2`, and `(t+u)/2`. The base radii are R, R, and `D=2L−R`. The limits allow `E→E₀>0` and merely bounded tangential variables, with complex normals `O(T_h)`; vanishing of the remainders divided by h is proved, not assumed.
- The real energy must remain in a positive compact interval. Replacing **the base action** `J(E_h,r)` by `J(E₀,r)` under `E_h-E₀=O(h)` need not preserve limiting ratio `1`: an order-one factor may remain, for example `exp(-ν s(E₀,r))` if `E_h=E₀+νh`. Retaining E_h in the action avoids this difficulty. No result for complex energy is claimed here.
- The proposition asserts neither a full expansion in powers of h nor uniformly differentiated remainders on fixed complex neighborhoods. Any uses of these assertions in the manuscript must be replaced individually. Holomorphy of the integral kernel is now available; deforming the spatial variables of the entire cell also requires control of the other factors and contours.
- A uniform relative `o(1)` kernel error can be inserted under oscillatory integrals only with control of their **normalized absolute integral**. [ComplexSaddleAbsolute.lean](../InfiniteZero/ComplexSaddleAbsolute.lean) already supplies this control for the normal saddles and a generic multiplier-insertion lemma. Verification of the other channel factors, particularly the atomic sources, remains separate.

**Correspondence with the Lean proofs.**

1. **Completed in Lean in `ComplexLandauKernel`.** The complex radial kernel is defined by the integral above; (4), its integrability, agreement with the real kernel, and domination of all measurable restrictions are proved.
2. `ComplexLandauEffectiveRadius` proves the quadratic radius defect. `BridgeActionTaylor` gives the global remainder `(b/4)(s-r)²`; `ComplexLandauAction` deduces (5), uniformly on positive compact sets.
3. `BridgeTimeRadial` controls the centers and `ComplexLandauTails` transfers the real tails. Their exponential decay absorbs every integer inverse power of h.
4. `ComplexLandauLocalProfile` proves (1), the identity with the normalized original integrand, Gaussian domination, and the integral limit for moving parameters and `δ/sqrt(h)→0`.
5. `ComplexLandauDecomposition` splits the actual integral exactly; `ComplexLandauAsymptotic` assembles the limits, divides by the positive coefficient, and proves compact uniformity, notably `tendstoUniformlyOn_complexLandauKernel_relative_rectangle`.
6. `ComplexLandauWindow` checks `T_h/sqrt(h)→0` and the required active-window perturbation criterion. The outer real tail is already controlled uniformly, including after complex normalization, in [LogFlatActiveRealTail.lean](../InfiniteZero/LogFlatActiveRealTail.lean#L92).
7. `ComplexLandauHolomorphic.analyticOnNhd_complexLandauKernel` proves radial holomorphy of the actual integral on `Re(z²)>0`, for fixed `b,h,E>0`. This is neither a hypothesis about an abstract extension nor a differentiated expansion uniform in h.
8. `ComplexCuspKernelProfile` applies the asymptotic to the three complex radii of the actual charts. The normalizer uses the linear normal term and moving real energy. In parallel, `ComplexCuspPhase` computes the polynomial magnetic-phase remainder: setting `a=s t²`, `d=r u²`, it is exactly

   \[
   \mathcal R_\Phi=\frac b4
   \bigl[2(R-L)(a+d)+\sqrt3\,tu+ua+td-\sqrt3\,ad\bigr].
   \]

   An explicit constant gives `|RΦ|≤C(|t|²+|u|²)` for bounded tangential variables and `|t|,|u|≤1`. The factor `exp(i RΦ/h)` therefore tends to `1` on the active window. These proofs contain no atomic amplitude.
9. `ComplexCuspKernelHolomorphic` proves joint holomorphy in `(t,u)` of the three actual compositions and their product. The theorem `exists_uniform_complexCuspKernel_bidisc` chooses a bidisc from `R>0`, `2L>R`, and the tangential bound, independently of `b,h>0` and the three positive real energies. This domain property is not a uniform differentiated asymptotic estimate.

This original analytic lemma is now verified in Lean; it was not introduced as a classical admission. It does not by itself prove the main theorem: sources and spectral transfer are separate steps.
