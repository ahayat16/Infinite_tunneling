# Global doublet and quantitative Schur correction

The first two min-max values of the constructed potential are now identified:

\[
 E_0=\min(E_+,E_-),\qquad E_1=\max(E_+,E_-).
\]

[ConstructedGlobalMinmax.lean](../InfiniteZero/ConstructedGlobalMinmax.lean) applies the actually constructed sectorial certificates to the original definitions of `groundEnergy` and `secondEnergy`. [ClassicalGlobalMinmax.lean](../InfiniteZero/ClassicalGlobalMinmax.lean) exports `doubleWell_global_minmax hp cert`, with only A002 and A004 as admissions: `∃T>0, ∀λ≥T, ∀L≥cert.L₀`. The parameters and threshold therefore precede separation and coupling. No spectral doublet is assumed.

The full connection is also compiled: [ParityDoubletRealization.lean](../InfiniteZero/ParityDoubletRealization.lean) constructs `TwoModeRealization`, then [ConstructedDoubleWellSpectral.lean](../InfiniteZero/ConstructedDoubleWellSpectral.lean) applies it to the explicit parameters. [ClassicalDoubleWellSpectral.lean](../InfiniteZero/ClassicalDoubleWellSpectral.lean) exports `doubleWell_twoModeRealization hp cert`: `∃T>0, ∀L≥cert.L₀`, `TwoModeRealization ... T`, and the actual `HasGapAboveGround` for every λ≥T. This directly supplies `LocalChannelAnalyticData.modes`. The corollary `doubleWell_spectral_realization hp cert` deduces `SpectralRealization`, with the same quantifiers and gap. Its classical ancestry is A002+A004; no double-well-specific spectral hypothesis is added.

## Operator decomposition and min-max values

[ParityOperatorDecomposition.lean](../InfiniteZero/ParityOperatorDecomposition.lean) lifts the parity projections to the actual domain and proves the mass and energy equalities between a vector and its two components. The sectorial lower bounds give the global lower bound `min(E+,E−)`. A normalized mode attains it; operator realization identifies it with the original test-function infimum.

Two separate arguments are needed for the second min-max value. [SecondEnergyParityUpper.lean](../InfiniteZero/SecondEnergyParityUpper.lean) chooses normalized tests approaching both sectorial infima. Their opposite parities give a space of dimension exactly two; mass and magnetic form are diagonal there, by [ParityTestFormOrthogonality.lean](../InfiniteZero/ParityTestFormOrthogonality.lean). Its Rayleigh upper bound approaches `max(E+,E−)`. The set defining the min-max is nonempty and bounded below, as proved in [SecondEnergyTestSpace.lean](../InfiniteZero/SecondEnergyTestSpace.lean).

Conversely, in each two-dimensional test space, the inner product with the lowest mode has a nonzero kernel. Positive mass allows normalization of this vector. The complement of the lowest mode is bounded below by the other energy, since the common sectorial complement bound exceeds both energies. This is the argument of [SecondEnergyComplementLower.lean](../InfiniteZero/SecondEnergyComplementLower.lean). [ParityGlobalMinmax.lean](../InfiniteZero/ParityGlobalMinmax.lean) assembles both inequalities. No eigenfunction is ever assumed to have compact support.

## Eigenspaces and actual gap

[ParityGroundEigenspaces.lean](../InfiniteZero/ParityGroundEigenspaces.lean) projects the actual eigenvalue equations. When the energies differ, the higher-sector component vanishes by its energy lower bound; sectorial simplicity gives exactly one global eigenline. When they coincide, each component belongs to its sectorial line, and the global eigenspace is exactly the plane spanned by the two modes.

[ParityGlobalGroundGap.lean](../InfiniteZero/ParityGlobalGroundGap.lean) proves `HasGapAboveGround` at the actual `groundEnergy`. If `E+<E−`, one may take `min(gap+,E−−E+)`; at a crossing, one may take `min(gap+,gap−)`. This is a positive gap at each coupling, not a uniform bound on the splitting, which vanishes at crossings. [PhysicalEigenmodeTransfer.lean](../InfiniteZero/PhysicalEigenmodeTransfer.lean) transfers the L² descriptions to classical eigenfunctions: smooth representatives turn almost-everywhere equality into pointwise equality. [PhysicalParityModes.lean](../InfiniteZero/PhysicalParityModes.lean) normalizes the certificates without changing their gap and synchronizes the same representatives: unit mass, opposite parities, and exact description of all eigenfunctions by one or two linear combinations. This formulation does not claim a spectral projection on an entire TeX window.

## Sectorial correction and relative estimate

[SchurGroundEnergyShift.lean](../InfiniteZero/SchurGroundEnergyShift.lean) retains, for the same root, the ground vector and quadratic bound on the difference from trial energy. On the actual parity restriction, [ParitySchurEnergyShift.lean](../InfiniteZero/ParitySchurEnergyShift.lean) identifies this root with `parityEnergy` and gives, for a unit trial q,

\[
 0\le a_\sigma-E_\sigma
 \le \frac{\|(H-E_{\rm ref})q_\sigma\|^2}{g}.
\]

[ConstructedParitySchurEnergyBound.lean](../InfiniteZero/ConstructedParitySchurEnergyBound.lean) proves that the hypotheses apply to the actual normalized trials of the constructed potential, with `g=γλ/8`, `Eref=Eatom`, and a threshold preceding λ and L. It holds for every atomic ground state and every domain representative of the trial. With [ParityTrialRayleigh.lean](../InfiniteZero/ParityTrialRayleigh.lean), the diagonal is exactly `Eatom+(δ±Reρ)/(1±s)`.

[ParityTrialResidualSquare.lean](../InfiniteZero/ParityTrialResidualSquare.lean) further proves, under `|s|≤1/2`, that each normalized trial residual satisfies `‖rσ‖²≤2(‖rL‖²+‖rR‖²)`, for the actual domain representatives. Together the results give the bound `16/(γλ)·(‖rL‖²+‖rR‖²)`; it is indeed the squared residuals that are used in comparison with the envelope.

Sharp control is now established through [reconstruction on the opposite support](OPPOSITE_SUPPORT_ESTIMATES.md). `PhysicalResidualMass` proves the exact identity between the squared translated residual and `λ⁴` times the mass of the product with the opposite potential, then the bound `4λ⁴` for each normalized trial. `AtomicOppositeSupportFineBounds` gives mass `≤C c²Γ² λ¹² exp(−2λ(G+J))` for the same references as the channels, with `G=J(Ecore,R)` and `J=J(Efull,2L−R)`.

The defect costs `λ¹⁴`, and the sectorial correction `λ¹⁵` after division by the gap. `OppositeSupportEnvelopeComparison` absorbs these powers and the saddle cost using the action margin `2(G+J)−(2G+J)=J>0`. `CanonicalParityRelativeErrors` deduces `δ=o(A)` and `σ±=o(A)` for the envelope of the same `W.c` and `W.Γ` as canonical hopping. Neither a new atomic reference nor a continuous eigenstate phase is assumed.

[Continuity of hopping](DILATION_AND_CONTINUITY.md) and splitting then allows the final connection. `ConstructedMainProof` constructs all original data from the explicit classical interfaces. In `Remaining`, `elementaryPotential_main` fixes the elementary potential, and `thm_main` concludes without a direct `sorry`. Its classical dependencies are exactly A002–A005; no spectral doublet or tunneling error is admitted.
