# Double-well overlap and parity trial states

The overlap of the two actual translated atomic states is exponentially small, uniformly for every separation \(L\ge4r_0\). The even and odd combinations can therefore be normalized beyond a coupling threshold independent of \(L\). These trials are distinct from the actual eigenmodes of the [spectral block](GLOBAL_PARITY_DOUBLET.md) constructed from them.

## Geometric bound without a spectral assumption

Let \(\phi\in L^2\) have mass \(1\), let \(d=(L,0)\), \(L\ge a>0\), and let \(\phi_L,\phi_R\) be the states defined by magnetic translation followed by inversion. Their pointwise norms are

\[
 |\phi_L(x)|=|\phi(x+d)|,\qquad
 |\phi_R(x)|=|\phi(d-x)|.
\]

Set \(S=\{x:\|x+d\|\ge a\}\). If \(x\notin S\), the triangle inequality and \(2L\ge2a\) give \(\|d-x\|\ge a\). Thus every point belongs to the exterior region of at least one state. Lebesgue changes of variables give

\[
 \int_S|\phi_L|^2\le M_a,\qquad
 \int_{S^c}|\phi_R|^2\le M_a,\qquad
 M_a=\int_{\|x\|\ge a}|\phi(x)|^2.
\]

Cauchy–Schwarz on both regions, with total mass \(1\), yields

\[
 |\langle\phi_L,\phi_R\rangle|
 \le2\sqrt{M_a},\qquad
 |\langle\phi_L,\phi_R\rangle|^2\le4M_a.
\]

[MagneticOverlapTail](../InfiniteZero/MagneticOverlapTail.lean) proves these inequalities for every square-integrable function, without assumptions of smoothness, radiality, or being an eigenstate.

## Application to the actual canonical state

[AtomicGroundAgmon](../InfiniteZero/AtomicGroundAgmon.lean) supplies, for the canonical ground state of the full potential,

\[
 M_{4r_0}\le {C_0\over\lambda^2}e^{-2d_0\lambda}.
\]

[CanonicalOverlapDecay](../InfiniteZero/CanonicalOverlapDecay.lean) deduces, with \(C=2\sqrt{C_0}>0\),

\[
 |s_{\lambda,L}|\le {C\over\lambda}e^{-d_0\lambda}
 \quad(L\ge4r_0),\qquad s_{\lambda,L}\longrightarrow0.
\]

The constants and threshold precede the choice of \(L\). For every \(\varepsilon>0\), a common threshold ensures \(|s_{\lambda,L}|<\varepsilon\) for all these separations. The theorem’s condition \(R<2L\) suffices, since the construction imposes \(8r_0<R\).

The [classical wrapper](../InfiniteZero/ClassicalCanonicalOverlapDecay.lean) requires only the elementary potential conditions. Its admissions are exactly A002 (operator realization) and A004 (unit-field radial spectral theorem). The full state, its tail, and the overlap inequality are proved consequences. A003 is not needed here.

## Canonical even and odd trials

Inversion exchanges the states. It also shows their inner product is real. For \(s=\langle\phi_L,\phi_R\rangle\),

\[
 \|\phi_L+\phi_R\|_2^2=2(1+s),\qquad
 \|\phi_L-\phi_R\|_2^2=2(1-s).
\]

[ParityTrialStates](../InfiniteZero/ParityTrialStates.lean) defines the trials by dividing by the positive square roots of these masses. When \(|s|<1\), they have mass \(1\), even and odd parity respectively, and are orthogonal. They are smooth when \(\phi\) is smooth. [CanonicalParityTrialStates](../InfiniteZero/CanonicalParityTrialStates.lean) applies these facts to the actual canonical state beyond a threshold uniform in \(L\), and proves linear independence.

## Residual and actual operator domain

The reference energy is that of the full atom, \(E_{\rm atom}\). Magnetic covariance gives exactly

\[
 (H_{\rm double}-E_{\rm atom})\phi_L
   =\lambda^2v(d-x)\phi_L,\qquad
 (H_{\rm double}-E_{\rm atom})\phi_R
   =\lambda^2v(x+d)\phi_R.
\]

[DoubleWellResidual](../InfiniteZero/DoubleWellResidual.lean) proves the differential identities. [DoubleWellTrialDomain](../InfiniteZero/DoubleWellTrialDomain.lean) proves that their \(L^2\) classes belong to the actual operator domain and satisfy the same residual identities there. The proof transports the closed single-well graph by adding the opposite potential, a bounded multiplication operator. Realization certificates are explicit classical inputs; no double-well spectral property is used.

[ParityTrialDomain](../InfiniteZero/ParityTrialDomain.lean) then transports the normalized sums and differences into the same domain. Their classes have the expected \(L^2\) parity and norm \(1\) when \(|s|<1\). The proof uses domain linearity and almost-everywhere representative identities. The actual self-adjoint restrictions and sectorial modes are now constructed separately in the [parity spectral block](PARITY_SPECTRAL_CONSTRUCTION.md). Trials and reconstructed eigenmodes remain distinct vectors.

## Exact quotients of normalized trials

For the same atomic state, define

\[
 \delta=\lambda^2\int v(-x+d)|\phi_L(x)|^2\,dx,\qquad
 \rho=\lambda^2\int\overline{\phi_L(x)}v(x+d)\phi_R(x)\,dx.
\]

The first number is `translatedDefect` and the second is exactly `hopping`. [ParityTrialRayleigh](../InfiniteZero/ParityTrialRayleigh.lean) proves in the actual operator domain

\[
 \operatorname{Re}\langle q_\pm,H_{\rm double}q_\pm\rangle
   =E_{\rm atom}+\frac{\delta\pm\operatorname{Re}\rho}{1\pm s},
 \qquad q_\pm=\frac{\phi_L\pm\phi_R}{\sqrt{2(1\pm s)}}.
\]

The preceding residuals give the matrix coefficients. Inversion identifies the two diagonal terms; symmetry identifies the real parts of the cross coefficients. L²/integral identities and all changes of representative are justified almost everywhere. The formula holds for every domain representative of the same trial whenever `|s|<1`, under continuity and boundedness of the potential and explicit operator realizations. No Schur-correction bound is assumed.

The specialization `canonicalParityTrial_schurDiagonal` uses the three physical objects already present in the transfer contract: `canonicalDefect`, `canonicalHopping`, and `canonicalOverlap`. The estimates `δ=o(A)` and `Σ±=o(A)` are now proved separately in [CanonicalParityRelativeErrors](../InfiniteZero/CanonicalParityRelativeErrors.lean), for the same amplitude as the canonical channels.

## Completed spectral connection and scope

Overlap convergence supplies one of the Schur-transfer inputs. The [coercive complement bound](TWO_WELL_COERCIVITY.md) is now established by IMS and the atomic gap, up to the actual operator domain. The first two min-max values are now identified with the minimum and maximum of the sectorial bottoms, with eigenspace descriptions and the global gap; see [GLOBAL_PARITY_DOUBLET.md](GLOBAL_PARITY_DOUBLET.md). Hopping continuity is also proved in [HoppingContinuity.lean](../InfiniteZero/HoppingContinuity.lean), with a threshold before separation; the wrapper `canonicalHopping_continuous` uses only A002 and A004. Continuity of the parity energies and their difference at all positive couplings is [proved by dilation](DILATION_AND_CONTINUITY.md).

The [opposite-support estimates](OPPOSITE_SUPPORT_ESTIMATES.md) retain the action margins of the source representation. They control the diagonal defect and, through the quadratic residual bound, the Schur corrections relative to the same amplitude. The absolute Agmon bound alone was insufficient for this step. The [final assembly](../InfiniteZero/ConstructedMainProof.lean) is compiled and [thm_main](../InfiniteZero/Remaining.lean) is proved modulo A002 and A004. Trials remain distinct from the actual eigenmodes constructed by spectral reduction.

## Verification

The transitive audit confirms that the conditional overlap bounds, canonical trials, and their domain transport use only standard Lean axioms. The two classical overlap corollaries depend exactly on A002 and A004, never on `thm_main`.

The additional module `ParityTrialRayleigh` compiles without warnings; its targeted audit verifies all ten theorems with only standard axioms. The global import and ten corresponding guards were added to `Verification`; `lake build InfiniteZero.Verification` passed after their addition. This integration did not regenerate the inventory or the historical global-check counts above.
