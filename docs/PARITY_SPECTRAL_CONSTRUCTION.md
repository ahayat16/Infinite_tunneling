# Spectral construction in the parity sectors

The chain through `DoubleWellParityGround` compiles: it constructs the actual ground states of both sectors for the explicit potential, identifies their energies with `parityEnergy`, and preserves a common absolute lower bound on their complements. The classical wrapper and continuity of the parity energies and splitting also compile. No new result is admitted. Inventories and the latest global check are recorded in [STATUS.md](STATUS.md), without assigning a completion percentage to the main theorem. The sector, min–max, and spectral wrappers depend on A002+A004; none depends on `thm_main`. The [global assembly](GLOBAL_PARITY_DOUBLET.md), normalized physical descriptions, and quadratic correction also compile.

## The actual restricted operator

Write `A = magneticOperator b λ (doubleWellPotential v L)` and let `J` be spatial inversion on L². In [L2ParitySectors.lean](../InfiniteZero/L2ParitySectors.lean), the sectors `K₊ = ker(J−I)` and `K₋ = ker(J+I)` are closed, complete subspaces; their orthogonal projections are exactly `(I±J)/2`. [DoubleWellInversionGraph.lean](../InfiniteZero/DoubleWellInversionGraph.lean) and [DoubleWellParityGraph.lean](../InfiniteZero/DoubleWellParityGraph.lean) prove that these projections preserve both coordinates of the actual closed graph of `A`, under the stated operator realization.

The general lemma in [ReducingSubspaceRestriction.lean](../InfiniteZero/ReducingSubspaceRestriction.lean) constructs the restriction `B` with domain `D(A) ∩ K`. For `u∈K`, graph invariance and uniqueness of the second coordinate give `Au∈K`, hence `Bu=Au`. The projection of `D(A)` is dense in `K`. Symmetry is inherited from `A`. Finally, for `y∈D(B*)`, continuity of `u↦⟨y,Bu⟩` composes with the continuous projection of the domains, and

\[
 \langle y,Ax\rangle=\langle y,A(P_Kx)\rangle.
\]

This places `y` in `D(A*)=D(A)`, hence in `D(B)`. The adjoint domains coincide and `B` is self-adjoint. [DoubleWellParityOperator.lean](../InfiniteZero/DoubleWellParityOperator.lean) exports self-adjointness, domain inclusion, equality of actions, and exact equivalence between the sector graph and the full graph on vectors of that parity. These are actual restrictions, with no additional domain postulated.

## From atomic trials to the sector complement

Let `φL,φR` be the magnetic translates of the same ground state of the full well, `s=⟨φL,φR⟩∈ℝ`, and

\[
 q_\pm=\frac{\phi_L\pm\phi_R}{\sqrt{2(1\pm s)}}.
\]

Uniform overlap decay gives `|s|≤1/2` at large coupling. These trials belong to the actual domain, have norm one, and have the required parity. [ParityTrialL2.lean](../InfiniteZero/ParityTrialL2.lean) shows that, in a fixed sector, `u⊥q±` implies `u⊥φL` and `u⊥φR`. [Two-well coercivity](TWO_WELL_COERCIVITY.md) therefore gives

\[
 \operatorname{Re}\langle u,Au\rangle
 \ge \bigl(E_{\rm atom}+\tfrac\gamma4\lambda\bigr)\|u\|^2
 \quad(u\in K_\pm,\ u\perp q_\pm),
 \qquad\gamma=\texttt{hRad.gap}.
\tag{1}
\]

This is `exists_parityTrial_complement_gap_of_radialData` in [ParityTrialCoercivity.lean](../InfiniteZero/ParityTrialCoercivity.lean). Its threshold is chosen before all couplings `λ≥T`, separations `L≥cert.L₀`, full-well ground states, and parity choices. The estimate is independent of the phase of that state.

The concrete assembly then uses an upper bound on the trial Rayleigh quotients. The residuals are exactly `λ²vRφL` and `λ²vLφR`; on their supports, the atomic tail gives an `O(λ exp(−dλ))` norm. Normalization costs at most one when `|s|≤1/2`. [ParityTrialEnergyBound.lean](../InfiniteZero/ParityTrialEnergyBound.lean) formalizes this control and places the diagonal below `E₀=Eatom+γλ/8`, leaving `g=γλ/8` in (1). Its threshold is independent of L, phase, and parity. This is not an estimate relative to the tunneling envelope.

## Exact physical Rayleigh quotients

[ParityTrialRayleigh.lean](../InfiniteZero/ParityTrialRayleigh.lean) now identifies the diagonal of that same normalized trial with the physical integrals:

\[
 a_\pm=E_{\rm atom}+\frac{\delta\pm\operatorname{Re}\rho}{1\pm s},\qquad
 \delta=\lambda^2\int v(-x+d)|\phi_L(x)|^2\,dx.
\]

Here `s=translatedOverlap`, `ρ=hopping`, and `δ=translatedDefect`, for the same normalized full-well ground state. Residuals in the actual domain give the diagonal entries `Eatom+δ`; inversion identifies the two diagonal integrals. The off-diagonal entry is exactly `Eatom*s+ρ`. Operator symmetry gives the same real part for the transposed entry. Expanding the sum or difference and dividing by `2(1±s)` proves the formula under `|s|<1`.

The result is universal over all actual domain vectors representing the trial, with a bounded continuous potential and explicit left, right, and double-well realizations. Changes of representatives are justified almost everywhere. It requires no asymptotic hypothesis or additional reality hypothesis on the hopping: only its real part enters the formula. `canonicalParityTrial_schurDiagonal` uses exactly `canonicalDefect`, `canonicalOverlap`, and `canonicalHopping`. The module compiles and is audited without admissions; small-correction estimates are neither its hypotheses nor its conclusions.

## Schur construction and an actual sector ground-state certificate

[ParitySchurGroundConstruction.lean](../InfiniteZero/ParitySchurGroundConstruction.lean) applies the already proved Schur construction to the self-adjoint restriction. Its abstract inputs are a unit trial in the actual domain, a diagonal `a≤E₀`, and a lower bound `E₀+g`, `g>0`, on its complement. It constructs `E≤E₀` and a `ParityGroundCertificate A even E`: a nonzero eigenvector in the original domain, a lower bound `E` throughout the sector, and a gap `E₀+g−E≥g` on the complement of the constructed vector. The absolute lower bound `E₀+g` is thus preserved. Existence of this certificate is a conclusion of the Schur argument, not a new admission.

[ParityGroundCertificate.lean](../InfiniteZero/ParityGroundCertificate.lean) deduces that the eigenspace **within this sector** has complex dimension one. Subtracting an eigenvector's projection onto the certified vector gives an orthogonal eigenvector; the gap forces it to vanish. Normalization and the operator realization produce an actual smooth eigenfunction of mass one with pointwise parity. The two sectors may have the same energy: sector simplicity does not exclude multiplicity two in the full space.

## The energy is the original infimum over test functions

`parityEnergy` is defined using normalized tests, rather than the certificate. [MagneticParityGraphLowerBound.lean](../InfiniteZero/MagneticParityGraphLowerBound.lean) projects the test-function graph by `(I±J)/2` and then passes to its closure. [MagneticParityNormalization.lean](../InfiniteZero/MagneticParityNormalization.lean) transfers a lower bound on normalized tests to all tests and then to the sector domain; zero mass is handled separately.

In [ParityEnergyIdentification.lean](../InfiniteZero/ParityEnergyIdentification.lean), existence of a nonzero domain vector also proves that the class of normalized tests of this parity is nonempty. The certified lower bound bounds this class from below. Its infimum applies to the eigenvector by graph closure, giving the reverse inequality. Thus

\[
 \texttt{parityEnergy}\ b\ v\ L\ \lambda\ \texttt{even}=E.
\]

No approximation of an eigenstate by compactly supported functions is admitted, and no arbitrary convention for the infimum of an empty set is used. The connection to continuity of the variational energies is described in [DILATION_AND_CONTINUITY.md](DILATION_AND_CONTINUITY.md).

## Absolute lower bound and scope of this stage

The strengthening `EigenvectorComplementBound` preserves the absolute lower bound `C=Eatom+γλ/4` on the complement of an actual eigenvector of energy `E<C`. For `u⊥w`, subtracting `a w` cancels the overlap with the trial. This increases the norm and leaves the shifted energy `⟨u,(A−E)u⟩` unchanged. Since `C−E>0`, the lower bound transfers without loss. This strengthening compiles and is used in the sector constructor.

[DoubleWellParityGround.lean](../InfiniteZero/DoubleWellParityGround.lean) now assembles the data for the constructed potential. Its conclusion is

\[
 \exists T>0,\ \forall\lambda\ge T,\ \forall L\ge L_0,\ \forall\sigma\in\{+,-\},
 \quad \exists c_\sigma:\texttt{ParityGroundCertificate}(H_{\lambda,L},\sigma,E_\sigma),
\]

with `Eσ = parityEnergy p.b p.potential L λ σ`, and

\[
 E_\sigma\le E_{\rm atom}+\tfrac\gamma8\lambda,\qquad
 c_\sigma.\mathrm{gap}\ge\tfrac\gamma8\lambda,\qquad
 E_\sigma+c_\sigma.\mathrm{gap}=E_{\rm atom}+\tfrac\gamma4\lambda.
\]

The potential parameters and separation certificate are fixed before this threshold, which is itself chosen before λ and L. The inputs are `BasicConditions`, `RadialCoreSpectralData`, and realizations of the core, full well, two translated wells, and double well. The conclusions assume no double-well mode or gap. The resulting eigenfunctions have mass one, are simple in their sector, and lie strictly below the common lower bound.

The global assembly now compiles in `ConstructedGlobalMinmax` and its wrapper `ClassicalGlobalMinmax`: the **first two global min–max levels** are exactly the minimum and maximum of the two sector bottoms, with a threshold preceding λ and L. `ParityOperatorDecomposition` lifts the projections to the actual domain; `ParityGroundEigenspaces` describes exactly one eigenline at the lower level or the plane of both modes at a crossing. `PhysicalParityModes` gives their normalized representatives and pointwise decompositions; `ParityGlobalGroundGap` preserves a positive gap.

[ParityDoubletRealization.lean](../InfiniteZero/ParityDoubletRealization.lean) assembles these facts into `TwoModeRealization`. [ConstructedDoubleWellSpectral.lean](../InfiniteZero/ConstructedDoubleWellSpectral.lean) applies it to the explicit potential. The wrapper [ClassicalDoubleWellSpectral.lean](../InfiniteZero/ClassicalDoubleWellSpectral.lean) first exports `doubleWell_twoModeRealization hp cert`: `∃T>0, ∀L≥cert.L₀, TwoModeRealization ... T`, with the actual `HasGapAboveGround` for all `λ≥T`. This package directly supplies `LocalChannelAnalyticData.modes`. The corollary `doubleWell_spectral_realization hp cert` replaces this package with `SpectralRealization`, preserving the gap and threshold. Only A002+A004 are instantiated.

The correction is now quantitative as well: `ParitySchurEnergyShift` and then `ConstructedParitySchurEnergyBound` give `0≤a±−E±≤‖(H−Eatom)q±‖²/(hRad.gap·λ/8)` for the actual trials. The physical Rayleigh-quotient identity is established. The diagonal defect and corrections are now `o(A(λ))` in `CanonicalParityRelativeErrors`, for the same envelope and witnesses as the hopping. Reconstruction on the opposite support preserves the required action margin; see [GLOBAL_PARITY_DOUBLET.md](GLOBAL_PARITY_DOUBLET.md). No description of the whole spectrum in a window or literal rank-two spectral projection as in T4.7 is claimed.

The classical inputs are the A002 realizations and the unit-field radial spectral theorem A004; the core spectral data are assembled from these inputs in Lean. No double-well spectral data are added to these admissions; A003 is not needed for this block. The wrapper [ClassicalDoubleWellParityGround.lean](../InfiniteZero/ClassicalDoubleWellParityGround.lean) instantiates them in `doubleWell_parityGrounds hp cert`. It exports `∃γ₀>0, ∃T>0, ∀λ≥T, ∀L≥L₀`, with energy ≤Eatom+γ₀λ, gap ≥γ₀λ, and exact lower bound Eatom+2γ₀λ, where γ₀=γ/8. The other two results, `doubleWell_parityEnergy_continuous` and `doubleWell_signedSplitting_continuous`, concern **all** strictly positive couplings at fixed admissible separation; see [DILATION_AND_CONTINUITY.md](DILATION_AND_CONTINUITY.md). This does not assert continuity of a choice of eigenfunctions. Continuity of canonical hopping is proved separately in `HoppingContinuity`, with the wrapper `canonicalHopping_continuous` under A002+A004.
The `ConstructedMainProof` assembly then applies the transfer and sign/intermediate-value arguments. `elementaryPotential_main` fixes the elementary potential, and `thm_main` is proved without its own `sorry`, modulo A002–A004. A003 enters the source and relative-error analysis, not the sector spectral construction above.
