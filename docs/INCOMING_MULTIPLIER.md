# Uniform multiplier for the incoming cell

The three actual Landau kernels, evaluated at the complex cusp radii, and their magnetic phase now have a uniform relative profile on the active normal window. The assembly uses the **actual core and full-atom energies**, with a proved quantitative energy error. Only the normal slope is replaced by its limit.

**Validation of the historical channel milestone.** The full `scripts/check.sh` check, including Lean reference export, passed after the physical assembly and canonical channels: 803 `assert_no_sorry` guards, 2033 proved results, four unchanged classical admissions, and one then-open final target.

The [full physical assembly of this integral](INCOMING_PHYSICAL_ASYMPTOTIC.md) now compiles separately: real truncation, substitutions with factor tStar⁶, two deformations, centering, and tangential integration. It concludes `N_h² Z_h incomingCuspIntegral → tStar⁶(π/β)Bs²`; the relative ratio tends to 1. The paragraphs below distinguish the scope of each intermediate step; the [connection to the cell and hopping](ACTIVE_CHANNEL_ASYMPTOTIC.md) and [thm_main assembly](../InfiniteZero/Remaining.lean) are now proved, with the four classical interfaces A002–A005 unchanged.

## Energies, actions, and quantifiers

Fix `p.BasicConditions`, L such that `R < 2L`, and the explicit interfaces `RadialCoreSpectralData p.b p`, `hAcore`, and `hApot`. Set

\[
 h=\lambda^{-1},\qquad D=2L-R>0,
\]
\[
 E_h^\circ=-h^2 E_{\rm core}(h^{-1}),\qquad
 E_h=\operatorname{scaledAtomicEnergy}(p,h^{-1}),
\]
\[
 A_h=2J_b(E_h^\circ,R)+J_b(E_h,D).
\]

The two energies are distinct. Each radial source kernel uses `Ecore = E_h°`, whereas the bridge uses `Efull = E_h`. `activeReferenceAction L Efull Ecore` preserves this argument order.

In [ActiveSaddleSlopeEnergy](../InfiniteZero/ActiveSaddleSlopeEnergy.lean), `exists_scaled_atomic_core_energy_linear_bounds_of_radialData` supplies a common threshold before λ, beyond which both energies belong to `[1/2,1]` and satisfy

\[
 |E_h^\circ-1|\le Bh,\qquad |E_h-1|\le Bh,
 \qquad B=\texttt{hRad.energyBound}.
\]

This bound follows from the spectral bounds already established. It is not an additional asymptotic-profile hypothesis. The conditional modules in this note invoke no admission; their application to classical data may supply these interfaces through A002 and A004. A003, identifying a resolvent, is unnecessary for these calculations on the kernel defined by its proper-time integral.

## Moving and fixed slopes

The definitions are

\[
 c_h=\frac{J_b'(E_h^\circ,R)+J_b'(E_h,D)}2-i\theta,
 \qquad
 c_*=\frac{J_b'(1,R)+J_b'(1,D)}2-i\theta,
\]
\[
 \theta=\frac{\sqrt3\,bL}{2},\qquad
 \Phi_*=\sqrt3\,bR(L-R/4).
\]

Here c_h denotes the moving complex slope, distinct from the real Schur coefficient denoted c_phys below. The Lean names are `movingActiveSaddleSlope` and `activeSaddleSlope`.

The exact calculation

\[
 J_b'(E,r)=\frac12\sqrt{b^2r^2+4E}
\]

gives, for `E,F ≥ 1/2`,

\[
 |J_b'(E,r)-J_b'(F,r)|\le |E-F|.
\]

This is `abs_deriv_bridgeAction_sub_energy_le`, uniform in r. Hence `‖c_h-c_*‖ ≤ Bh` for the physical energies.

The window used in Lean is

\[
 T_h=\texttt{logFlatActiveWindow}(t_*,h)=t_*h^{3/4},
\]

and the theorem is uniform over `|s|,|r| ≤ s₀`, `‖t‖,‖u‖ ≤ M T_h`, for every **M fixed before h**. On this domain,

\[
 \left\|\frac{(c_*-c_h)(t+u)}h\right\|
 \le 2BM T_h\longrightarrow0.
\]

[ComplexCuspFrozenSlope](../InfiniteZero/ComplexCuspFrozenSlope.lean) therefore proves

\[
 \exp((c_*-c_h)(t+u)/h)\longrightarrow1
\]

uniformly. Mere convergence `E_h° → 1`, `E_h → 1` would not justify this step: the slope error is multiplied by the divergent factor `T_h/h`. The proved `O(h)` bound provides the required control.

## Profile of the three kernels and the phase

The complex radii come from the actual polynomials `complexCuspPlus`, `complexCuspMinus`, and `complexBridge`. Their linear terms are respectively `t/2`, `u/2`, and `(t+u)/2`. Their remainders are uniformly quadratic for bounded tangential parameters; `T_h²/h → 0` allows insertion into the exponentials.

[ComplexCuspKernelProductProfile](../InfiniteZero/ComplexCuspKernelProductProfile.lean) combines three relative profiles of the actual kernel and the phase correction `exp(i complexCuspPhaseRemainder / h)`. The exact polynomial phase has the form

\[
 \Phi(t,u,s,r)=\Phi_*+\theta(t+u)+O(|t|^2+|u|^2+|tu|)
\]

on the small domain considered. The results `tendsto_complexCuspKernelPhaseProfile` and `eventually_complexCuspKernelPhaseProfile_uniform` give relative convergence to 1, then a uniform bound by 2. The first holds along convergent parameter families; the second exports a single threshold for all s,r,t,u in the window.

Write

\[
 k_{p,h}=\texttt{landauLeadingCoefficient}(b,E_h^\circ,R),
 \qquad
 k_{b,h}=\texttt{landauLeadingCoefficient}(b,E_h,D).
\]

[AtomicCuspKernelProfile](../InfiniteZero/AtomicCuspKernelProfile.lean) defines `frozenCuspKernelPhaseProfile` by multiplying the previous profile by the slope-freezing factor. Its exact identity `frozenCuspKernelPhaseProfile_eq_normalized_product` reads

\[
 P_h^*(t,u,s,r)=
 \frac{h^{9/2}}{k_{p,h}^2k_{b,h}}
 \exp\!\left(\frac{A_h+c_*(t+u)-i\Phi_*}{h}\right)
 \mathcal K_h(t,u,s,r)e^{i\Phi(t,u,s,r)/h},
\]

where 𝒦_h is the product of the three actual complex kernels at the two effective energies. The theorem `eventually_atomic_frozenCuspKernelPhaseProfile_uniform_of_radialData` proves `P_h* → 1` uniformly throughout the window; the corollary `eventually_norm_atomic_frozenCuspKernelPhaseProfile_le_two_of_radialData` bounds it by 2.

Neither A_h, k_{p,h}, nor k_{b,h} is frozen at energy 1. The results export a uniform `o(1)` error; they do not claim the `O(log(1/h)⁻¹)` rate of Proposition P6.7.

## Real integrability and four-coordinate Fubini

[CuspSourcePairingFubini](../InfiniteZero/CuspSourcePairingFubini.lean) defines `incomingCuspDensity p L h Ecore Efull t u s r`. This density contains the Jacobians t²u², two log-flat factors, cutoffs `χa(t)χa(u)χb(s)χb(r)`, two radial kernels, and the bridge kernel with its phase. `incomingCuspDensity_eq_complex` identifies it exactly with the product of the three complex kernels restricted to real coordinates.

The `logFlat` profile is zero at the tip and equals `exp(-β log²(t*/t))` for `t>0`. This extension is essential to the continuity proof on the closed rectangle; its value at zero is not replaced by formally evaluating an expression involving division by zero.

Throughout the closed rectangle `0≤t,u≤t₀`, `|s|,|r|≤s₀`, the basic geometric conditions imply

\[
 \|\Psi_+(t,s)\|,\|\Psi_-(u,r)\|\ge R>0,
 \qquad \|\Psi_+(t,s)+\Psi_-(u,r)-2d\|\ge 2L-R>0.
\]

Continuity of the three kernels at these positive radii gives continuity of the density on this compact set, hence joint absolute integrability. `integrableOn_incomingCuspDensity_chartProduct` and `integrableOn_incomingCuspDensity_normalProduct` expose the two groupings. The permutation of the four coordinates is proved to preserve products of restricted measures, and Fubini is then applied to integrands whose integrability is already established.

The two physical formulas are `incoming_sourceCell_eq_normals_first` and `incoming_sourceCell_eq_tangents_first`. Under hp, `R<2L`, `h>0`, and `Ecore,Efull>0`, they assume only that φ is continuous and has the exact tail `φ(x)=Γ K_b(h,Ecore,‖x‖)` for `‖x‖>r₀`. They retain the same φ, Γ, and real scalar c_phys and give

\[
 I_{+-}^{\rm in,in}
 =-h^2(h^{-2}\varepsilon a\,c_{\rm phys}\Gamma)^2
   \int\!\int\!\int\!\int \texttt{incomingCuspDensity}.
\]

The permitted orders are `(t,u,s,r)` and `(s,r,t,u)`. `integrableOn_incomingCuspDensity_normals` also proves integrability in `(t,u)` **for every** `(s,r)∈[-s₀,s₀]²`, rather than merely almost everywhere. No integrability witness is added to the hypotheses of these formulas.

## Signs, complex square, and passage to the active integral

The formulas agree with TeX references `sublemma:P6-7-prefactor`, `sublemma:P6-7-real-germ`, and `sublemma:P6-7-joint-phase`: each incoming source is negative, their product is positive, and the exterior factor −h² retains the cell's negative sign. Each source is h⁻² times an h⁻³ᐟ² radial kernel, and the bridge supplies another h⁻³ᐟ². The total power is

\[
 2-\frac72-\frac72-\frac32=-\frac{13}{2}.
\]

After the profile identity, the extracted factor is therefore `−ε²a²c_phys²Γ² h⁻¹³ᐟ² k_{p,h}² k_{b,h} exp(−A_h/h) exp(iΦ*/h)`. The slope sign is `c*=α−iθ`, consistent with the positive phase `exp(iΦ/h)` of the actual `sourceKernel`.

Conjugating the first source in `sourcePairing` does not produce a conjugated factor in the normal model: the incoming source considered is real on the real contour. That same real germ is extended. Both normal models therefore have slope c*, and their product is **`I_h(c*)²`**, then the square of the complex saddle amplitude. The squared modulus appears in the positive envelope, not in place of this complex product. The variables s,r remain real.

The `t_*h³ᐟ⁴` window differs from the TeX window `M₀h log(1/h)`. It contains the saddle and suffices for uniform `o(1)` control of the quadratic remainders. To use holomorphy, the normals must first be restricted to a region where the real cutoff χa is identically 1; no holomorphic extension of an arbitrary C∞ cutoff is assumed. No holomorphic extension of the atomic correction η is involved.

Real truncation of the **coupled cell**, the two successive normal deformations, their connectors, and endpoints are assembled in [AtomicIncomingNormalAsymptotic](../InfiniteZero/AtomicIncomingNormalAsymptotic.lean). Insertion of the uniform remainder under an **absolute** bound for the product of contour integrals is now proved in `CuspSaddleMultiplier`, as detailed below. The existing scalar tail and contour-norm estimates alone do not prove this for the coupled physical product. A small uniform error on the real contour cannot be divided directly by a complex integral subject to oscillatory cancellation.

[LogFlatContourMultiplier](../InfiniteZero/LogFlatContourMultiplier.lean) already proves `logFlatComplex_multiplier_ray_shift`. For a complex-differentiable multiplier B bounded by K on the closed half-strip `{z | a ≤ re z, im z ∈ uIcc 0 v}`, and `F(z)=logFlatComplexIntegrand β k C z * B(z)`, its exact identity is

\[
 \int_a^\infty F(x)\,dx
 =i\int_0^v F(a+i y)\,dy+\int_a^\infty F(x+i v)\,dx.
\]

Integrability on rays and connectors follows from the hypotheses. A Gaussian majorant makes the right connector vanish as its real coordinate tends to infinity, at fixed parameters. B is not assumed holomorphic on all of ℂ. This identity retains the left connector; by itself it does not assert uniform smallness on the saddle scale as h varies.

Holomorphy of the normalized physical profile, successive application to both variables, and bounds on the left connectors are proved. Together with evaluation of the saddle product, they establish the required content of `sublemma:P6-7-one-contour`, `sublemma:P6-7-product-contour`, and `sublemma:P6-7-evaluation`. The [physical assembly](INCOMING_PHYSICAL_ASYMPTOTIC.md) and [channels](ACTIVE_CHANNEL_ASYMPTOTIC.md) establish the incoming asymptotic used in the final proof, without claiming the stronger TeX rates.

## Holomorphy and integrated error on the saddle contour

[CuspKernelProfileHolomorphic](../InfiniteZero/CuspKernelProfileHolomorphic.lean) proves joint holomorphy of `frozenCuspKernelPhaseProfile` on the three-radius domain. Its normalized identity is a product of entire exponential factors and the three already holomorphic kernels. The common bidisc radius depends only on the geometry; it is chosen before h and both positive energies.

[CuspSaddleMultiplier](../InfiniteZero/CuspSaddleMultiplier.lean) uses the actual critical point y_c and normals

\[
 t(q)=t_*e^{-(y_c+q)},\qquad
 S_h=(\log(t_*/T_h)-\operatorname{Re}y_c,\infty)^2.
\]

On S_h, both normals have modulus at most T_h. The physical multiplier is continuous there and bounded by 2. The scalar contour product is integrable; multiplying it by this profile preserves integrability. This is a Lean conclusion, not a hypothesis of the error lemma.

Write F_h(q_1,q_2) for the product of the two logarithmic integrands, N_h for the scalar normalizer, and P_h for the physical profile composed with the normals t(q_1),t(q_2). The exported result is, uniformly in s,r,

\[
 N_h^2\left(\int_{S_h}F_hP_h-\int_{S_h}F_h\right)\longrightarrow0.
\]

The proof applies the already established absolute bound \(\lvert N_h\rvert^2\int_{S_h}|F_h|\le C_\beta\) to the small uniform profile error. It does not divide by an oscillatory integral. The moving domain S_h is allowed by the bound uniform over every measurable restriction of the product contour.

This normalization still concerns the **logarithmic** integral. The two physical substitutions t=t_*e^{-y} and u=t_*e^{-z} each contribute t_*³, hence a total factor t_*⁶. The normalized logarithmic model product tends to π/β, not 1. The identity \(\lvert N_h\rvert^2 S_G(h)^2=t_*^6\pi/\beta\) retains these factors in the connection to the physical envelope.

## Tangential coefficient and connector with amplitude

[CuspTangentialMass](../InfiniteZero/CuspTangentialMass.lean) proves \(s_0\le B_s=\int\chi_b\le2s_0\), the identity of the double tangential integral with B_s², and positivity of \(k_0(b,1,R)^2k_0(b,1,D)B_s^2\). The coefficient at the two moving energies converges to this fixed coefficient, and their ratio tends to 1.

[LogFlatMultiplierConnector](../InfiniteZero/LogFlatMultiplierConnector.lean) preserves the favorable exponential gain on the left connector after multiplication by a bounded amplitude. It uses the sector bound at the critical point, rather than the coarse bound in terms of the complex parameter's modulus. At the T_h boundary, decay is on the scale \(\exp(-t_*\operatorname{Re}(c_*)h^{-1/4})\). The multiplied connector is negligible after scalar normalization. Its insertion into the coupled physical deformation remains separate from this estimate.

## Exact identity for the normalized physical density

[IncomingCuspDensityNormalization](../InfiniteZero/IncomingCuspDensityNormalization.lean) relates the real density to the two scalar integrands and physical profile: for t,u>0,

\[
 \mathcal N_h\,\mathrm{density}_h(t,u,s,r)
 =\chi_a(t)\chi_a(u)\chi_b(s)\chi_b(r)
   f_h(t)f_h(u)P_h(t,u,s,r).
\]

Here f_h is `complexLogFlatIntegrand` with m=2 and fixed slope c*, and the normalization retains the moving energies:

\[
 \mathcal N_h=
 \frac{(h^{3/2})^3}{k_0(b,E_c,R)^2k_0(b,E_f,D)}
 \exp\bigl((A_{\rm ref}-i\Phi_*)/h\bigr).
\]

The identity is multiplicative; its proof does not divide by this normalization and therefore does not assume it is nonzero. The powers t²u² are exactly those of the two Jacobians. The factor −h² and source strengths remain outside this density, and t*⁶ appears only in the later logarithmic substitutions. This algebraic identity assumes neither positive energy nor positive h; only t,u>0 are required.
