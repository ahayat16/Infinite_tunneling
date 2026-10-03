# From the incoming term to canonical channels

This step turns the [physical-integral asymptotic](INCOMING_PHYSICAL_ASYMPTOTIC.md) into an asymptotic for the full active cell. It retains the actual core and full-potential energies in the action. It does not construct the double-well modes or gap.

## Complex normalization and source factors

Write \(h=\lambda^{-1}\), and \(G_h\) for `logFlatSaddleLeading`,

\[
 K_h=k_b(E_c(h),R)^2 k_b(E_f(h),2L-R)B_s^2,
 \qquad K_*=k_b(1,R)^2 k_b(1,2L-R)B_s^2>0.
\]

The complex identity is

\[
 N_hG_h=t_*^3\sqrt{\pi/\beta},\qquad
 N_h^2G_h^2=t_*^6\pi/\beta.
\]

This is a complex square: replacing either factor with its conjugate would remove the oscillation. The physical-integral model is

\[
 M_h={K_h\over(h^{3/2})^3}
 \exp\bigl((-A_h+i\Phi_*)/h\bigr)G_h^2.
\]

The physical normalization satisfies the exact identity

\[
 N_h^2Z_hM_h=t_*^6(\pi/\beta)B_s^2\ne0.
\]

The already-proved relative limit defines a remainder \(e_0(h)\to0\) and gives \(I_h=M_h(1+e_0(h))\). This remainder depends neither on the chosen radial state nor on the factors \(c,\Gamma\).

The exact source formula multiplies this integral by

\[
 -h^2(h^{-2}\varepsilon a c\Gamma)^2.
\]

The real identity

\[
 {h^{-2}\over(h^{3/2})^3}
 =\lambda^6\sqrt\lambda
\]

gives the envelope prefactor. There is no division by \(c\) or \(\Gamma\), and the identities remain valid when these coefficients vanish.

## Phase and choice of envelope

We use the real phase

\[
 \Theta(\lambda)=\lambda\Phi_*+
 2\,\mathrm{logFlatSaddlePhase}(\beta,2,t_*,c_*,\lambda^{-1}).
\]

It is continuous on a half-line and

\[
 \Theta(\lambda)/\lambda\longrightarrow\Phi_*.
\]

The identity \(G_h=|G_h|e^{i\theta_h}\), with the explicit positive prefactor, avoids any new choice of argument branch. The quotient \(K_h/K_*\) tends to \(1\). Absorbing it into the remainder gives

\[
 I_{\mathrm{in,in}}(\lambda)
 =-K_*\,\mathrm{activeSaddleEnvelope}(\lambda,c,\Gamma)
 e^{i\Theta(\lambda)}(1+e(\lambda)),\qquad e(\lambda)\to0.
\]

The ratio of the squared saddle sizes, using the Gaussian and the manuscript’s complex Hessian, also tends to \(1\). Absorbing it into the remainder replaces `activeSaddleEnvelope` with `activeSaddleTexEnvelope`. The factor \(t_*^6\pi/\beta\) is already present in the squared scalar size; it is not multiplied into \(K_*\) a second time.

This variant supplies a relative error \(o(1)\), sufficient for the oscillation argument. It does not claim the manuscript’s stronger rate \(O(1/\log\lambda)\).

## A single choice of witnesses and canonical errors

The active reduction supplies, for each large coupling, the same actual atomic states, \(c_\lambda\in[1/2,1]\), \(\Gamma_\lambda>0\), and exact radial tail. The inactive estimates hold universally in these witnesses. We can therefore choose them once and set

\[
 a(\lambda)=K_*\,
 \mathrm{activeSaddleTexEnvelope}(\lambda,c_\lambda,\Gamma_\lambda)>0.
\]

The relative bounds for active replacement and inactive cells are

\[
 {C_{\rm sc}\over K_*}e^{-(\beta/8)\log^2\lambda}\to0,
 \qquad
 {C_{\rm inact}\over K_*}e^{-15\,\mathrm{hopMargin}\,\lambda}\to0.
\]

The incoming identity and these bounds then give the eight limits in `ChannelAsymptotics`: one active complex limit and seven inactive zero limits. The sign is

\[
 I_{12}(\lambda)/a(\lambda)+e^{i\Theta(\lambda)}\longrightarrow0.
\]

Neither the amplitude nor the witnesses need be continuous for this structure. Continuity of hopping and splitting, required by the final theorem, is proved separately in [HoppingContinuity](../InfiniteZero/HoppingContinuity.lean) and by [sector dilation](DILATION_AND_CONTINUITY.md).

## Scope and verification

The classical inputs remain explicit: magnetic realization, radial spectral data, and interior elliptic estimate. The resolvent representation of hopping additionally uses the universal classical Landau interface. No tunneling asymptotic is taken as a classical input.

The main declarations are:

- [IncomingCellAsymptotic](../InfiniteZero/IncomingCellAsymptotic.lean): exact relative identity for the incoming cell, uniform in the witnesses.
- [IncomingCellTexAsymptotic](../InfiniteZero/IncomingCellTexAsymptotic.lean): conversion to the manuscript envelope, with remainder tending to zero.
- [ConcreteChannelWitnesses](../InfiniteZero/ConcreteChannelWitnesses.lean): common choice of actual states and both coefficients.
- [CanonicalChannelAsymptotics](../InfiniteZero/CanonicalChannelAsymptotics.lean): actual construction of the channels and formula for genuine hopping.
- [ClassicalCanonicalChannelAsymptotics](../InfiniteZero/ClassicalCanonicalChannelAsymptotics.lean): `canonicalHopping_asymptotic` and `exists_canonicalHopping_asymptotic_separation`, under `BasicConditions`.

The two classical wrappers have exactly A002, A003, A004, and A005 as transitive admissions, with no dependency path to `thm_main`. The other declarations take the classical interfaces explicitly and their proofs use only standard Lean/Mathlib axioms. The [global spectral realization](GLOBAL_PARITY_DOUBLET.md), continuity results, and [relative parity errors](../InfiniteZero/CanonicalParityRelativeErrors.lean) are now proved. Their [assembly](../InfiniteZero/ConstructedMainProof.lean) concludes `thm_main`, with the fixed witness `elementaryParameters` in [Remaining.lean](../InfiniteZero/Remaining.lean), modulo the four classical interfaces A002–A005.

At the historical channel milestone, the full check `bash scripts/check.sh` had completed successfully: 3892 build tasks, 803 `assert_no_sorry` guards, then export of 2033 proved theorems, 376 definitions/contracts, four direct admissions, 26 dependent wrappers, and one final target then still open. The 256 blueprint entries and the graphs had been regenerated. These numbers do not measure the completed proportion of the final theorem’s proof.
