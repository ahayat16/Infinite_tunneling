# Asymptotic of the physical incoming integral

**Normalized physical limit proved.** The density and normalization identities, real truncation, logarithmic substitutions, both contour displacements, and saddle evaluation have compiled. The assembly [AtomicIncomingNormalAsymptotic](../InfiniteZero/AtomicIncomingNormalAsymptotic.lean) and connection [IncomingCuspTangentialIntegration](../InfiniteZero/IncomingCuspTangentialIntegration.lean) also compile without warnings. [AtomicIncomingIntegralAsymptotic](../InfiniteZero/AtomicIncomingIntegralAsymptotic.lean) assembles the limit below, proves the coefficient nonzero, and proves convergence of the relative quotient to 1. Its targeted audit confirms no `sorry` and only standard axioms. The final `sourceCell` asymptotic and its canonical connection are now proved in the [channel assembly](ACTIVE_CHANNEL_ASYMPTOTIC.md). The [final assembly](../InfiniteZero/ConstructedMainProof.lean) and [thm_main](../InfiniteZero/Remaining.lean) are now compiled modulo the two classical admissions A002 and A004.

Fix `p.BasicConditions`, a distance `L` with `R < 2L`, and explicit data `hRad`, `hAcore`, `hApot`. Thresholds as \(h\to0^+\) precede both tangential variables \(s,r\in[-s_0,s_0]\). The proofs use these interfaces as arguments; they add no tunneling-specific admission. A002 supplies the realizations; the radial data are assembled from A002+A004.

## Normalization and target formula

Write \(h=\lambda^{-1}\), \(D=2L-R\), and retain both actual energies

\[
 E_h^\circ=-h^2E_{\rm core}(h^{-1}),\qquad
 E_h=\operatorname{scaledAtomicEnergy}(p,h^{-1}),\qquad
 A_h=2J_b(E_h^\circ,R)+J_b(E_h,D).
\]

Set \(k_{c,h}=k_b(E_h^\circ,R)\), \(k_{f,h}=k_b(E_h,D)\), where \(k_b\) is `landauLeadingCoefficient`, and

\[
 Z_h=\frac{h^{9/2}}{k_{c,h}^2k_{f,h}}
       \exp\!\left(\frac{A_h-i\Phi_*}{h}\right),\qquad
 B_s=\int_{-s_0}^{s_0}\chi_b(s)\,ds.
\]

`Z_h` is exactly `incomingCuspNormalization`. It contains neither source strength nor the sign of `sourcePairing`. The complex slope

\[
 c_*=\frac{J_b'(1,R)+J_b'(1,D)}2-i\theta
\]

is `activeSaddleSlope`; it differs from the real Schur coefficient \(c_{\rm phys}\). For \(w_h=\texttt{logFlatSaddleRoot}(\beta,2,t_*,c_*,h)\), \(y_h=w_h-3/(2\beta)\), we use

\[
 f_h(y)=\beta y^2+\frac{c_*t_*}{h}e^{-y}+3y,
 \qquad N_h=\sqrt{\Re w_h}\,e^{f_h(y_h)}.
\]

The proved conclusion of this assembly is the **complex** limit

\[
 N_h^2 Z_h\,
 \texttt{incomingCuspIntegral}(p,L,h,E_h^\circ,E_h)
 \longrightarrow t_*^6\frac{\pi}{\beta}B_s^2.
\]

The square \(N_h^2\) is a complex square. Both normal factors have the same slope \(c_*\): their product is not a squared modulus. The actions and three radial coefficients remain evaluated at the moving energies.

## Natural-language proof and Lean connections

1. **Physical density and integrability.** [CuspSourcePairingFubini](../InfiniteZero/CuspSourcePairingFubini.lean) defines `incomingCuspDensity`, with Jacobians \(t^2u^2\), four cutoffs, two core kernels, and the bridge kernel with its phase. Joint integrability on the four-coordinate rectangle is proved; normal integrability is also proved for every tangential pair in the closed rectangle. Fubini can therefore change the integration order. The identity `incomingCuspNormalization_mul_density` in [IncomingCuspDensityNormalization](../InfiniteZero/IncomingCuspDensityNormalization.lean) gives exactly the product of two scalar normal models and the actual `frozenCuspKernelPhaseProfile`. No \(t_*^6\) occurs at this stage.

2. **Real truncation before deformation.** On the real box, the density is bounded by
   
   \[
   C h^{-6}e^{-A_h/h}t^2u^2e^{-(t+u)/(8h)}.
   \]

   With \(T_h=t_*h^{3/4}\), the exterior of \((0,T_h)^2\) therefore costs at most \(C h^{-6}e^{-A_h/h}t_0^6e^{-(t_*/8)h^{-1/4}}\). [AtomicIncomingRealTruncation](../InfiniteZero/AtomicIncomingRealTruncation.lean) proves that this error tends to zero after multiplication by \(N_h^2Z_h\). Polynomial losses and logarithmic growth of the normalizer are absorbed by the stretched exponential. For sufficiently small \(h\), \(\chi_a=1\) on \([0,T_h]\).

3. **Two exact substitutions.** [IncomingCuspLogarithmicChange](../InfiniteZero/IncomingCuspLogarithmicChange.lean) performs \(t=t_*e^{-x}\), \(u=t_*e^{-y}\). The factors \(t^2dt\), \(u^2du\) give \(t_*^3e^{-3x}dx\), respectively \(t_*^3e^{-3y}dy\), after reversing the endpoints. This yields exactly \(t_*^6\), with \(x,y>a_h=\tfrac34\log(1/h)\). The normal cutoff has already been removed on this window; no holomorphic continuation of a smooth cutoff is used.

4. **Two Cauchy displacements with the actual profile.** [AtomicCuspRayShift](../InfiniteZero/AtomicCuspRayShift.lean) supplies fiberwise identities. Holomorphy on a bidisk and a uniform profile bound by \(2\) are proved at the actual energies. [AtomicCuspDoubleRayShift](../InfiniteZero/AtomicCuspDoubleRayShift.lean) proves integrability of all hybrid contours, then successively shifts both rays to height \(v_h=\Im w_h\). The left connectors give a uniform error
   
   \[
   C\exp\!\left(-t_*\Re\(c_*\)h^{-1/4}\right),
   \]

   negligible even after multiplication by \(N_h^2\). Fiberwise bounds are integrated using Fubini; no hybrid integrability is left as an additional analytic hypothesis.

5. **Centering, saddle, and integrated error.** [AtomicCuspContourTranslation](../InfiniteZero/AtomicCuspContourTranslation.lean) translates real coordinates by \(\Re y_h\), without an additional Jacobian. The domain becomes \((a_h-\Re y_h,\infty)^2=\texttt{activeSaddleProductDomain}\). [CuspSaddleLeading](../InfiniteZero/CuspSaddleLeading.lean) proves that the model product, multiplied by \(N_h^2\), tends to \(\pi/\beta\). Removal of the left tail is justified quantitatively. The absolute product bound allows integration of the uniform error of the actual multiplier, which tends to \(1\). The limit therefore remains \(\pi/\beta\), uniformly in \(s,r\).

6. **Tangential integration.** The normal assembly gives \(\chi_b(s)\chi_b(r)t_*^6\pi/\beta\) uniformly. `norm_incomingCuspIntegral_sub_tangential_le` is proved: a uniform error \(\delta\) gives integrated error at most \(\delta(2s_0)^2\). The cutoff product integrates exactly to \(B_s^2\), and [CuspTangentialMass](../InfiniteZero/CuspTangentialMass.lean) proves \(s_0\le B_s\le2s_0\). The limiting coefficient is therefore strictly positive.

## Outer factors and completed connections

The exact incoming-cell identity, with the same radial state \(\phi^\circ_h\) and exterior coefficient \(\Gamma_h\), is

\[
 \operatorname{sourceCell}_{12}(c_{\rm phys}\phi^\circ_h)
 =-h^2\bigl(h^{-2}\varepsilon a c_{\rm phys}\Gamma_h\bigr)^2
   \texttt{incomingCuspIntegral}(p,L,h,E_h^\circ,E_h).
\]

The negative sign and strengths of both sources remain outside the density. The constant phase is retained exactly in \(Z_h\); its inversion restores \(e^{i\Phi_*/h}\), to combine with the phase of \(N_h^{-2}\). The prefactor \(h^{-13/2}=\lambda^6\sqrt\lambda\) then follows from \(h^{-2}h^{-9/2}\). This algebraic calculation is now formalized in `IncomingPrefactorIdentity` and `IncomingCellAsymptotic`.

The [connection to canonical channels and hopping](ACTIVE_CHANNEL_ASYMPTOTIC.md) is now proved, reusing scattered and inactive remainders controlled with the same witnesses. The [double-well spectral reduction](GLOBAL_PARITY_DOUBLET.md), [relative errors](../InfiniteZero/CanonicalParityRelativeErrors.lean), and continuity needed for crossings are also proved. The [assembly](../InfiniteZero/ConstructedMainProof.lean) constructs the data required by the contracts. Potential parameters remain fixed before the separation threshold and then every L beyond it. [Remaining.lean](../InfiniteZero/Remaining.lean) explicitly fixes `elementaryParameters` in `elementaryPotential_main` and deduces `thm_main`.

## Completed connection to the active channel

The formalized identity retains the same real coefficients c and Γ without dividing by them. Set

\[
 K_*=\texttt{activeTangentialLeadingCoefficient}(p,L)>0,\qquad
 \Theta(\lambda)=\lambda\Phi_*+
 2\,\texttt{logFlatSaddlePhase}(\beta,2,t_*,c_*,\lambda^{-1}).
\]

The proved connection is

\[
 I_{\rm in,in}(\lambda)
 =-K_*\,\texttt{activeSaddleEnvelope}(p,L,\lambda,c,\Gamma)
   e^{i\Theta(\lambda)}(1+e(\lambda)),\qquad e(\lambda)\to0.
\]

The remainder comes from the already-proved relative quotient and is independent of c, Γ, and the representative chosen for the exact tail. The complex normalization identity proved in `ComplexSaddleNormalization` is

\[
 N_h\,\texttt{logFlatSaddleLeading}(\beta,k,t_*,c_*,h)
 =t_*^{k+1}\sqrt{\pi/\beta}.
\]

Its norm version is in `SaddleNormalizationIdentity`. Squaring for k=2 absorbs the factor tStar⁶ exactly. `logFlatSaddleLeading_eq_size_mul_phase` supplies the continuous real phase; `tendsto_activeTangentialLeadingCoefficient_relative` replaces the three moving coefficients by their positive limit, absorbing the quotient into e. The action A_h must retain the actual energies.

`exists_continuousOn_logFlatSaddlePhase_inv` and `tendsto_logFlatSaddlePhase_inv_div` then supply eventual continuity of Θ and limiting slope Φ*. The ratio of the envelopes using `Re w` and `1+w` already tends to 1. This variant targets relative error o(1), sufficient for oscillation arguments; it does not claim the text’s stronger rate O(1/log λ). The final connections are proved in `IncomingCellTexAsymptotic`, then `CanonicalChannelAsymptotics`, with the TeX envelope and explicit Gaussian phase.
