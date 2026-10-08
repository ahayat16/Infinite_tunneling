import InfiniteZero.Construction
import InfiniteZero.SpectralAssembly
import InfiniteZero.HoppingPhase
import InfiniteZero.GroundSpaceAlgebra
import InfiniteZero.ConstructionNonradial
import InfiniteZero.ConstructionCompact
import InfiniteZero.OperatorBridge
import InfiniteZero.LinearPhase
import InfiniteZero.ConstructionExistence
import InfiniteZero.ParityTransfer
import InfiniteZero.HoppingSourceIdentity
import InfiniteZero.HoppingIntegrability
import InfiniteZero.LandauResolventBridge

/-!
# The three conclusions of the main theorem and their analytic assembly

There is no admission in this file. The final proof in `Remaining.lean`
constructs the needed local data via `ConstructedMainProof`, using only the
documented classical interfaces. None of the structures below asserts its
own existence.

For statement review, start with `MainConclusion`: its fields translate the
three items of the active `thm:main` in
`Infinite_Zero_Tunneling_Lean_oriented_V2.tex`. The physical definitions are
in `MagneticModel.lean`; `OperatorMainConclusion` in `OperatorMain.lean`
adds their interpretation for the actual unbounded operator on complex L².
The structures `LocalAnalyticData`, `LocalChannelAnalyticData` and
`FixedAnalyticData` organize intermediate proofs. They are not assumptions
of the final `thm_main`.
-/

noncomputable section
open Set Filter
open scoped Topology
open scoped ContDiff

namespace InfiniteZero

/-- Intermediate outputs for one separation. In the fixed-potential pipeline,
the hopping fields are derived from `LocalChannelAnalyticData` below. -/
structure LocalAnalyticData (b : ℝ) (v : Potential) (L slope : ℝ) where
  threshold : ℝ
  atomic_exists : ∀ coupling, threshold ≤ coupling → ∃ φ, IsAtomicGroundState b v coupling φ
  atomic_simple : ∀ coupling, threshold ≤ coupling → AtomicGroundSimple b v coupling
  modes : TwoModeRealization b v L threshold
  ground_gap : ∀ coupling, threshold ≤ coupling →
    HasGapAboveGround (magneticOperator b coupling (doubleWellPotential v L))
      (groundEnergy b v L coupling)
  hopping_real : ∀ coupling, threshold ≤ coupling → (canonicalHopping b v L coupling).im = 0
  hopping_asymptotic : LinearCosineAsymptotic
    (fun coupling => -(canonicalHopping b v L coupling).re) slope
  schur : CanonicalParitySchurData b v L hopping_asymptotic.amplitude
  continuity_threshold : ℝ
  splitting_continuous : ContinuousOn (fun x => oddEnergy b v L x - evenEnergy b v L x)
    (Ici continuity_threshold)
  hopping_continuous : ContinuousOn (fun x => (canonicalHopping b v L x).re)
    (Ici continuity_threshold)

/-- A source-channel formulation of the analytic inputs for the cusp potential. The complex
active-cell estimate, seven inactive-cell estimates and Schur component
estimates are exposed separately. The source resolvent identity follows from
the universal classical kernel contract and atomic existence. The final cosine
formula and signed-splitting transfer are proved consequences, not fields here. -/
structure LocalChannelAnalyticData (p : CuspParameters) (L slope : ℝ) where
  threshold : ℝ
  channels : ChannelAsymptotics (canonicalSourceCell p L) slope
  channels_threshold : channels.threshold ≤ threshold
  coupling_pos : 0 < channels.threshold
  scaled_energy_pos : ∀ x, channels.threshold ≤ x → 0 < scaledAtomicEnergy p x
  atomic_exists : ∀ x, channels.threshold ≤ x → ∃ φ, IsAtomicGroundState p.b p.potential x φ
  atomic_simple : ∀ x, threshold ≤ x → AtomicGroundSimple p.b p.potential x
  modes : TwoModeRealization p.b p.potential L threshold
  ground_gap : ∀ x, threshold ≤ x →
    HasGapAboveGround (magneticOperator p.b x (doubleWellPotential p.potential L))
      (groundEnergy p.b p.potential L x)
  schur : CanonicalParitySchurData p.b p.potential L (fun x => 2 * channels.amplitude x)
  continuity_threshold : ℝ
  splitting_continuous : ContinuousOn
    (fun x => oddEnergy p.b p.potential L x - evenEnergy p.b p.potential L x)
    (Ici continuity_threshold)
  hopping_continuous : ContinuousOn (fun x => (canonicalHopping p.b p.potential L x).re)
    (Ici continuity_threshold)

/-- The source resolvent representation is derived from a universal classical
kernel interface, rather than assumed for this specific atomic state. -/
theorem LocalChannelAnalyticData.resolvent_representation {p : CuspParameters} {L slope : ℝ}
    (h : LocalChannelAnalyticData p L slope) (hp : p.BasicConditions)
    (hKernel : HasPositiveLandauResolvent p.b) (x : ℝ) (hx : h.channels.threshold ≤ x) :
    RightResolventRepresentation p.b p.potential L x (scaledAtomicEnergy p x)
      (canonicalAtomicState p.b p.potential x) := by
  have hpos : 0 < x := h.coupling_pos.trans_le hx
  exact rightResolventRepresentation_of_freeLandauResolventKernel
    (hKernel x (scaledAtomicEnergy p x) hpos (h.scaled_energy_pos x hx))
    (CuspParameters.potential_contDiff hp) (CuspParameters.potential_hasCompactSupport hp)
    (canonicalAtomicState_spec p.b p.potential x (h.atomic_exists x hx)) hpos rfl L

theorem LocalChannelAnalyticData.cells_integrable {p : CuspParameters} {L slope : ℝ}
    (h : LocalChannelAnalyticData p L slope) (hp : p.BasicConditions) (hL : p.R < 2 * L)
    (x : ℝ) (hx : h.channels.threshold ≤ x) :
    CellsIntegrable p L x⁻¹ (scaledAtomicEnergy p x)
      (canonicalAtomicState p.b p.potential x) :=
  cellsIntegrable_of_continuous hp hL (inv_pos.mpr (h.coupling_pos.trans_le hx))
    (h.scaled_energy_pos x hx) (canonicalAtomicState_contDiff p.b p.potential x).continuous

def LocalChannelAnalyticData.toLocalAnalyticData {p : CuspParameters} {L slope : ℝ}
    (h : LocalChannelAnalyticData p L slope) (hp : p.BasicConditions)
    (hKernel : HasPositiveLandauResolvent p.b) (hL : p.R < 2 * L) :
    LocalAnalyticData p.b p.potential L slope where
  threshold := h.threshold
  atomic_exists := fun x hx => h.atomic_exists x (h.channels_threshold.trans hx)
  atomic_simple := h.atomic_simple
  modes := h.modes
  ground_gap := h.ground_gap
  hopping_real := fun x hx => canonicalHopping_real_of_resolvent p L x
    (h.resolvent_representation hp hKernel x (h.channels_threshold.trans hx))
    (h.cells_integrable hp hL x (h.channels_threshold.trans hx))
  hopping_asymptotic := canonicalHopping_linearCosine_of_resolvent p L slope
    h.channels (h.cells_integrable hp hL) (h.resolvent_representation hp hKernel)
  schur := h.schur
  continuity_threshold := h.continuity_threshold
  splitting_continuous := h.splitting_continuous
  hopping_continuous := h.hopping_continuous

/-- The potential and separation threshold precede the choice of L.  The
analytic thresholds in `localData` may depend on that later choice of L. -/
structure FixedAnalyticData where
  parameters : CuspParameters
  basic : parameters.BasicConditions
  L₀ : ℝ
  separation : parameters.R < L₀
  localData : ∀ L, L₀ ≤ L → LocalChannelAnalyticData parameters L
    (Geometry.phaseStar parameters.b parameters.R L)

/-- All admissibility properties are proved from the elementary conditions,
including the smooth zero extension at the cusp tips. -/
def FixedAnalyticData.admissible (h : FixedAnalyticData) :
    AdmissiblePotential h.parameters.potential :=
  CuspParameters.admissiblePotential h.basic

/-- The conclusions of the active TeX `thm:main` for one fixed field `b`,
one fixed single-well potential `v`, and one fixed half-separation `L`.
Throughout, `coupling` is the manuscript's λ, and the well centers are
separated by `2 * L` as in `eq:double-well-unscaled`.

The first two fields ensure that the canonical hopping coefficient really
uses a normalized atomic ground state and is independent of its choice.
The remaining fields encode (i) infinitely many exact lowest-level crossings
and multiplicity two at every sufficiently large crossing, (ii) infinitely
many zeros of the complex hopping coefficient, and (iii) interlaced even
and odd simple ground states.

Here energies are defined by variational infima/min-max, and eigenfunctions
are smooth L² solutions of the concrete differential equation. Their
operator interpretation is supplied by `OperatorMainConclusion`; the
definitions alone do not assert a spectral identification. In particular,
the proof establishes that the first two min-max values are the minimum
and maximum of the actual even/odd ground energies at large coupling
(`ConstructedGlobalMinmax.lean`).

Each threshold and each sequence below may depend on the already fixed `L`.
The two zero sequences need not coincide. Neither their spacing nor
uniqueness of a zero between successive parity samples is asserted. -/
structure MainConclusion (b : ℝ) (v : Potential) (L : ℝ) : Prop where
  /-- At all sufficiently large λ, `canonicalAtomicState` is a normalized
  ground state of the single-well Hamiltonian `h_v(λ)` from
  `eq:one-well-unscaled`. This rules out its default zero branch there. -/
  atomic_states : ∃ T, ∀ coupling, T ≤ coupling →
    IsAtomicGroundState b v coupling (canonicalAtomicState b v coupling)
  /-- For large λ, every normalized atomic ground state gives the same
  complex hopping `ρ_λ` of `eq:rho-intro`, with the same state used in both
  shifted wells. Thus the canonical choice introduces no phase ambiguity. -/
  hopping_intrinsic : ∃ T, ∀ coupling, T ≤ coupling → ∀ φ,
    IsAtomicGroundState b v coupling φ →
      canonicalHopping b v L coupling = hopping b v L coupling φ
  /-- TeX `thm:main` (i), the zero sequence: distinct positive couplings,
  strictly increasing to infinity, at which the second min-max value equals
  the variational bottom. These are `E₁(λ_n) = E₀(λ_n)` after the proved
  low-energy identification. -/
  spectral_zeros : ∃ z : ℕ → ℝ,
    StrictMono z ∧ Tendsto z atTop atTop ∧
    ∀ n, 0 < z n ∧ secondEnergy b v L (z n) - groundEnergy b v L (z n) = 0
  /-- TeX `thm:main` (i), multiplicity clause: at every sufficiently large
  zero of this gap, the full classical L² ground eigenspace has complex
  dimension two and contains normalized even and odd eigenfunctions.
  This covers all large crossings, not just the sequence above. -/
  large_crossings : ∃ T, ∀ coupling, T ≤ coupling →
    secondEnergy b v L coupling - groundEnergy b v L coupling = 0 → GroundSpaceExactlyTwo b v L coupling
  /-- TeX `thm:main` (ii): a separate strictly increasing positive sequence
  tending to infinity with `ρ_λ = 0` in ℂ. The assertion is about the whole
  coefficient, not just its real part or its leading asymptotic term. -/
  hopping_zeros : ∃ z : ℕ → ℝ,
    StrictMono z ∧ Tendsto z atTop atTop ∧
    ∀ n, 0 < z n ∧ canonicalHopping b v L (z n) = 0
  /-- TeX `thm:main` (iii), expressed by alternating samples:
  `0 < p_n < q_n < p_(n+1)`, with both sequences tending to infinity.
  At `p_n` the full ground space is one-dimensional and even, and at `q_n`
  it is one-dimensional and odd. Parity means inversion `x ↦ -x`. -/
  parity_changes : ∃ p q : ℕ → ℝ,
    Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
    ∀ n, 0 < p n ∧ p n < q n ∧ q n < p (n + 1) ∧
      SimpleGroundParity b v L (p n) true ∧ SimpleGroundParity b v L (q n) false

namespace LocalAnalyticData

/-- The transfer conclusion is derived from the physical Rayleigh/Schur
equations and their component estimates, rather than supplied as an input. -/
def asymptotics {b L slope : ℝ} {v : Potential} (h : LocalAnalyticData b v L slope) :
    LinearSpectralAsymptotics (evenEnergy b v L) (oddEnergy b v L)
      (fun coupling => (canonicalHopping b v L coupling).re) slope where
  hopping := h.hopping_asymptotic
  transfer := CanonicalParitySchurData.transfer h.hopping_asymptotic h.schur
  threshold := h.continuity_threshold
  splitting_continuous := h.splitting_continuous
  hopping_continuous := h.hopping_continuous

/-- Dimensions and parities are deduced algebraically from the exact mode
decompositions, rather than assumed as numerical dimension fields. -/
def spectral {b L slope : ℝ} {v : Potential} (h : LocalAnalyticData b v L slope) :
    SpectralRealization b v L h.threshold := h.modes.toSpectralRealization

theorem physical_gap {b L slope : ℝ} {v : Potential} (h : LocalAnalyticData b v L slope)
    {coupling : ℝ} (hcoupling : h.threshold ≤ coupling) :
    secondEnergy b v L coupling - groundEnergy b v L coupling =
      lowGap (evenEnergy b v L) (oddEnergy b v L) coupling := by
  rw [h.spectral.ordered_second coupling hcoupling, h.spectral.ordered_ground coupling hcoupling]
  rfl

/-- All of the final IVT, exact-zero, dimension and parity assembly is checked. -/
theorem conclusion {b L slope : ℝ} {v : Potential} (h : LocalAnalyticData b v L slope)
    (hSlope : 0 < slope) :
    MainConclusion b v L := by
  let T := max 0 h.threshold
  have hT (x : ℝ) (hx : T < x) : h.threshold ≤ x :=
    le_trans (le_max_right _ _) hx.le
  have hpos (x : ℝ) (hx : T < x) : 0 < x :=
    lt_of_le_of_lt (le_max_left _ _) hx
  have result := (h.asymptotics.toSpectralAsymptotics hSlope).result_above T
  constructor
  · refine ⟨h.threshold, fun coupling hcoupling => ?_⟩
    exact canonicalAtomicState_spec b v coupling (h.atomic_exists coupling hcoupling)
  · refine ⟨h.threshold, fun coupling hcoupling φ hφ => ?_⟩
    exact canonicalHopping_eq_hopping b v L coupling (h.atomic_simple coupling hcoupling) φ hφ
  · obtain ⟨z, hm, ht, hz⟩ := result.gap_zeros
    refine ⟨z, hm, ht, fun n => ⟨hpos _ (hz n).1, ?_⟩⟩
    rw [h.physical_gap (hT _ (hz n).1)]
    exact (hz n).2
  · refine ⟨h.threshold, fun coupling hcoupling hz => ?_⟩
    rw [h.physical_gap hcoupling, lowGap_eq_zero_iff] at hz
    exact h.spectral.crossing coupling hcoupling hz
  · obtain ⟨z, hm, ht, hz⟩ := result.hopping_zeros
    refine ⟨z, hm, ht, fun n => ⟨hpos _ (hz n).1, ?_⟩⟩
    apply Complex.ext
    · exact (hz n).2
    · simpa only [Complex.zero_im] using h.hopping_real (z n) (hT _ (hz n).1)
  · obtain ⟨p, q, hp, hq, hs⟩ := result.interlaced_signs
    refine ⟨p, q, hp, hq, fun n => ?_⟩
    obtain ⟨hn, hpq, hqp, hpositive, hnegative⟩ := hs n
    refine ⟨hpos _ hn, hpq, hqp, ?_, ?_⟩
    · exact h.spectral.even_lower (p n) (hT _ hn) (sub_pos.mp hpositive)
    · exact h.spectral.odd_lower (q n) (hT _ (lt_trans hn hpq))
        (sub_neg.mp hnegative)

end LocalAnalyticData

theorem LocalChannelAnalyticData.conclusion {p : CuspParameters} {L slope : ℝ}
    (h : LocalChannelAnalyticData p L slope) (hp : p.BasicConditions)
    (hKernel : HasPositiveLandauResolvent p.b) (hL : p.R < 2 * L)
    (hSlope : 0 < slope) :
    MainConclusion p.b p.potential L :=
  (h.toLocalAnalyticData hp hKernel hL).conclusion hSlope

/-- Variational/classical version of the existential statement in TeX
`thm:main`: choose positive `b`, positive `L₀` and one admissible `v` before
requiring the three conclusions for every `L ≥ L₀`. The final result uses
the stronger `ConstructedPotentialMainTheorem`, which also specifies the
core-plus-cusps construction and the unbounded-operator interpretation. -/
def MainTheorem : Prop :=
  ∃ b L₀ : ℝ, ∃ v : Potential,
    0 < b ∧ 0 < L₀ ∧ AdmissiblePotential v ∧ ∀ L, L₀ ≤ L → MainConclusion b v L

/-- Quantifier-correct conditional assembly, with the analytic data as an explicit
argument. `#print axioms` contains no `sorryAx` for this theorem. -/
theorem thm_main_of_analytic_data (h : FixedAnalyticData)
    (hKernel : HasPositiveLandauResolvent h.parameters.b) : MainTheorem := by
  refine ⟨h.parameters.b, h.L₀, h.parameters.potential, h.basic.b_pos, ?_,
    h.admissible, fun L hL => (h.localData L hL).conclusion h.basic hKernel
      (by linarith [h.basic.radius_pos, h.separation])
      (CuspParameters.phase_pos h.basic h.separation hL)⟩
  exact lt_trans h.basic.radius_pos h.separation

end InfiniteZero
