import InfiniteZero.OperatorMain
import InfiniteZero.AtomicSourceRegime
import InfiniteZero.AtomicGroundAgmon
import InfiniteZero.AtomicGroundComparison
import InfiniteZero.RadialCoreExteriorState
import InfiniteZero.RadialCoreNormalizationLower
import InfiniteZero.AtomicGroundWeightedDecomposition
import InfiniteZero.AtomicGroundFineDecomposition
import InfiniteZero.ConstructedMainProof
import InfiniteZero.ClassicalEllipticInterior

/-!
# The constructed-potential theorem and the permitted classical admissions

The original source, saddle, spectral and relative-error estimates are
proved in the imported modules. `elementaryPotential_main` fixes the explicit
parameter witness before the separation and coupling. `thm_main` follows
from that stronger statement and has no direct admission.

Statement-review entry point: read `elementaryPotential_main` for the
literal fixed potential, or `thm_main` for the existential formulation of
the active TeX `thm:main`. Their conclusion is unfolded in
`OperatorMain.lean` and `Main.lean`; the potential and its concrete parameter
values are in `Construction.lean` and `ConstructionParameters.lean`.
Docstrings there match the TeX labels rather than equation numbers, which
may change when the manuscript is compiled. The full comparison and its
scope are recorded in `docs/STATEMENT_AUDIT.md`.

The remaining admissions are the four documented classical interfaces:
operator realization, free Landau resolvent, radial-core harmonic data and
the fixed-ball elliptic estimate. Their transitive use is checked by the
audit. `AnalyticConstructionProblem` retains an older intermediate contract;
the final proof uses the constructed `LocalAnalyticData` route instead.
-/

namespace InfiniteZero

open scoped ContDiff Topology
open MeasureTheory

/-- Historical intermediate contract, with parameters fixed before L.
This definition does not assert its own existence and is not used as an
assumption in the final proof. -/
def AnalyticConstructionProblem : Prop := Nonempty FixedAnalyticData

/-- A002: standard essential self-adjointness, test-function core, variational
identification and elliptic regularity for a smooth bounded real potential.
This does not use the cusp construction or any tunneling result.
References and natural proof: docs/CLASSICAL_OPERATOR_REALIZATION.md. -/
theorem magnetic_realization (b coupling : ℝ) (V : Potential)
    (hsmooth : ContDiff ℝ ∞ V) (hbounded : ∃ C : ℝ, ∀ x, |V x| ≤ C) :
    IsMagneticRealization b coupling V := by
  sorry

/-- A003: the free Landau resolvent kernel for all positive field, coupling,
and spectral-energy parameters, all smooth `L²` solutions and all smooth
compactly supported sources. No potential or tunneling estimate occurs here.
Reference: Cornean--Fournais--Frank--Helffer, Ann. Inst. Fourier 63 (2013),
equation (B.21), p. 2508, followed by the semigroup Laplace transform.
Detailed signs, scaling, domain argument and natural proof:
docs/CLASSICAL_LANDAU_RESOLVENT.md. -/
theorem free_landau_resolvent_kernel {b coupling E : ℝ}
    (hb : 0 < b) (hCoupling : 0 < coupling) (hE : 0 < E) :
    FreeLandauResolventKernel b coupling E := by
  sorry

/-- A004: the classical one-well harmonic approximation, specialized to the
explicit radial core. It supplies the ground state, its O(coupling) energy
excess, the first spectral gap, expressed on the original test core, and
a positive radial normalized ground-state choice (Theorem 1.1(2)).
Helffer--Kachmar, arXiv:2208.13030v5, Theorem 1.1 (pp. 3--4), Proposition 2.1
(p. 11), and the oscillator gap (p. 12). Scaling, min-max, realization and
test-function identifications: docs/RADIAL_HARMONIC_CONTRACT.md.
No cusp, source, nonradial gap or tunneling estimate occurs in this input. -/
theorem radial_core_spectral_data (b : ℝ) (p : CuspParameters)
    (hb : 0 < b) (hr : 0 < p.r₀) : Nonempty (RadialCoreSpectralData b p) := by
  sorry

/-- The genuine normalized positive radial core state has the exact exterior
Landau tail. Only the classical one-well data A004 are admitted: reduction
of the concrete Hamiltonian, polar integrability and exterior uniqueness
are proved in Lean. No bound on the normalization coefficient is asserted. -/
theorem CuspParameters.radialCore_kernel {p : CuspParameters} {b : ℝ}
    (hb : 0 < b) (hr : 0 < p.r₀) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ ∧
        ∃ Γ : ℝ, 0 < Γ ∧ ∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ) := by
  exact CuspParameters.exists_radialCore_kernel_of_radialData hb hr
    (Classical.choice (radial_core_spectral_data b p hb hr))

/-- A polynomial lower bound for the coefficient of the same genuine radial
core state and its exact exterior tail. The constants precede the coupling.
Only A002 and A004 are used: the normalization estimate itself is proved.
With h = coupling⁻¹ this gives Γ ≥ c h² and Γ⁻¹ ≤ C h⁻². -/
theorem CuspParameters.radialCore_normalization_lower {p : CuspParameters} {b : ℝ}
    (hb : 0 < b) (hr : 0 < p.r₀) :
    ∃ c > 0, ∃ C > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ ∧
        ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ)) ∧
          c * (coupling⁻¹) ^ 2 ≤ Γ ∧ Γ⁻¹ ≤ C * coupling ^ 2 := by
  apply CuspParameters.exists_radialCore_kernel_coefficient_bounds_of_radialData hb hr
    (Classical.choice (radial_core_spectral_data b p hb hr))
  intro coupling
  apply magnetic_realization b coupling p.core (CuspParameters.core_contDiff hr)
  refine ⟨1, fun x => ?_⟩
  have hx := CuspParameters.core_range p x
  rw [abs_le]
  exact ⟨hx.1, hx.2.trans (by norm_num)⟩

/-- The actual constructed potential has a simple isolated atomic ground
state at all sufficiently large couplings. The proof uses A002 and the
radial-only A004; the nonradial construction is proved in Lean. -/
theorem CuspParameters.eventual_atomicGround_properties {p : CuspParameters}
    (hp : p.BasicConditions) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      AtomicGroundSimple p.b p.potential coupling ∧
      HasGapAboveGround (magneticOperator p.b coupling p.potential)
        (atomicGroundEnergy p.b p.potential coupling) ∧
      atomicGroundEnergy p.b p.potential coupling ≤ atomicGroundEnergy p.b p.core coupling := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  apply CuspParameters.eventual_atomicGround_properties_of_radialData hp hRad
  · intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := CuspParameters.core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  · intro coupling
    exact magnetic_realization p.b coupling p.potential
      (CuspParameters.admissiblePotential hp).smooth
      (CuspParameters.admissiblePotential hp).bounded

/-- For the explicit potential the scaled atomic energy tends to one, and
the genuine canonical ground state admits the source representation at every
sufficiently large coupling, uniformly in the separation parameter.
Only the three documented classical interfaces are admitted. -/
theorem CuspParameters.atomic_source_regime {p : CuspParameters}
    (hp : p.BasicConditions) :
    Filter.Tendsto (scaledAtomicEnergy p) Filter.atTop (𝓝 1) ∧
      ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → AtomicSourceFacts p coupling := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := CuspParameters.core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential := by
    intro coupling
    exact magnetic_realization p.b coupling p.potential
      (CuspParameters.admissiblePotential hp).smooth
      (CuspParameters.admissiblePotential hp).bounded
  refine ⟨CuspParameters.tendsto_scaledAtomicEnergy_of_radialData hp hRad hAcore hApot,
    CuspParameters.exists_atomicSourceFacts_of_radialData hp hRad hAcore hApot ?_⟩
  exact fun _ _ hCoupling hE => free_landau_resolvent_kernel hp.b_pos hCoupling hE

/-- Exponential exterior decay of the actual canonical ground state of the
constructed potential. Only the general realization A002 and the radial
harmonic approximation A004 are admitted; the nonradial Agmon estimate and
its application to this ground state are proved in Lean. -/
theorem CuspParameters.canonicalAtomicState_agmon_tail {p : CuspParameters}
    (hp : p.BasicConditions) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsAtomicGroundState p.b p.potential coupling
        (canonicalAtomicState p.b p.potential coupling) ∧
      (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖},
        ‖canonicalAtomicState p.b p.potential coupling x‖ ^ 2) ≤
        (C / coupling ^ 2) * Real.exp (-2 * d * coupling) := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  apply CuspParameters.exists_canonicalAtomicState_agmon_tail_of_radialData hp hRad
  · intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := CuspParameters.core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  · intro coupling
    exact magnetic_realization p.b coupling p.potential
      (CuspParameters.admissiblePotential hp).smooth
      (CuspParameters.admissiblePotential hp).bounded

/-- The actual radial and full ground energies are exponentially close, with
only A002 and the radial-only A004 admitted. The cusp perturbation estimate
and the Schur comparison are proved from the explicit potential. -/
theorem CuspParameters.atomicGroundEnergy_exponential_comparison {p : CuspParameters}
    (hp : p.BasicConditions) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      0 ≤ atomicGroundEnergy p.b p.core coupling - atomicGroundEnergy p.b p.potential coupling ∧
      atomicGroundEnergy p.b p.core coupling - atomicGroundEnergy p.b p.potential coupling ≤
        C * Real.exp (-d * coupling) := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  apply CuspParameters.exists_atomicGroundEnergy_exponential_comparison_of_radialData hp hRad
  · intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := CuspParameters.core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  · intro coupling
    exact magnetic_realization p.b coupling p.potential
      (CuspParameters.admissiblePotential hp).smooth
      (CuspParameters.admissiblePotential hp).bounded

/-- Genuine normalized ground vectors of the core and full potential are
exponentially close after fixing their relative phase by positive overlap.
All estimates specific to the constructed potential are proved in Lean. -/
theorem CuspParameters.atomicGroundVectors_exponential_comparison {p : CuspParameters}
    (hp : p.BasicConditions) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ u v : L2Space, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
        u ∈ operatorEigenspace (magneticOperator p.b coupling p.core)
          (atomicGroundEnergy p.b p.core coupling) ∧
        v ∈ operatorEigenspace (magneticOperator p.b coupling p.potential)
          (atomicGroundEnergy p.b p.potential coupling) ∧
        ‖v - u‖ ≤ C * Real.exp (-d * coupling) ∧
        0 < (inner ℂ u v).re ∧ (inner ℂ u v).im = 0 := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  apply CuspParameters.exists_atomicGroundVectors_exponential_comparison_of_radialData hp hRad
  · intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := CuspParameters.core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  · intro coupling
    exact magnetic_realization p.b coupling p.potential
      (CuspParameters.admissiblePotential hp).smooth
      (CuspParameters.admissiblePotential hp).bounded

/-- Genuine smooth core and full ground states admit a common weighted
decomposition. Its coefficient is in [1/2,1], its correction is orthogonal
to the positive radial core, and both its weighted mass and exact differential
equation are proved. Only the classical A002 and A004 are admitted.
This absolute decay does not assert the fine tunneling-scale source estimates. -/
theorem CuspParameters.atomicGround_weighted_decomposition {p : CuspParameters}
    (hp : p.BasicConditions) :
    ∃ χ : CuspParameters.CuspWeightCutoffs p,
      ∃ κ₀ > 0, ∃ C > 0, ∃ d > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Set.Icc (1 / 2 : ℝ) 1,
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          waveInner φ η = 0 ∧
          (∀ κ ∈ Set.Icc 0 κ₀,
            mass (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * η x) ≤
              C ^ 2 * Real.exp (-2 * d * coupling)) ∧
          ∀ x : Plane,
            magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x =
              -((c * coupling ^ 2 : ℝ) : ℂ) * (p.atomicPerturbation x : ℂ) * φ x +
                ((c * (atomicGroundEnergy p.b p.potential coupling -
                  atomicGroundEnergy p.b p.core coupling) : ℝ) : ℂ) * φ x := by
  let χ := Classical.choice (CuspParameters.exists_cuspWeightCutoffs hp)
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := CuspParameters.core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential := by
    intro coupling
    exact magnetic_realization p.b coupling p.potential
      (CuspParameters.admissiblePotential hp).smooth
      (CuspParameters.admissiblePotential hp).bounded
  obtain ⟨_, _, _, κ₀, hκ₀, C, hC, d, hd, threshold, hthreshold, hstates⟩ :=
    CuspParameters.exists_atomicGround_weighted_decomposition_of_radialData
      hp hRad hAcore hApot χ
  exact ⟨χ, κ₀, hκ₀, C, hC, d, hd, threshold, hthreshold, hstates⟩

/-- The genuine core/full decomposition has an exact-action and log-flat
weighted bound. Only the classical realizations A002 and radial data A004
are admitted. The original fine forcing and response estimates are proved.
This is an L² result; derivatives and pointwise scattered-source estimates
remain open. The same radial coefficient and normalization are retained. -/
theorem CuspParameters.atomicGround_fine_weighted_decomposition {p : CuspParameters}
    (hp : p.BasicConditions) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) :
    ∃ χ : CuspParameters.CuspWeightCutoffs p,
      ∃ κ₀ > 0, ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Set.Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          waveInner φ η = 0 ∧
          (∀ κ ∈ Set.Icc 0 κ₀,
            mass (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * η x) ≤
              (C * c * Γ * coupling ^ 3 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2) ∧
          ∀ x : Plane,
            magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x =
              -((c * coupling ^ 2 : ℝ) : ℂ) * (p.atomicPerturbation x : ℂ) * φ x +
                ((c * (atomicGroundEnergy p.b p.potential coupling -
                  atomicGroundEnergy p.b p.core coupling) : ℝ) : ℂ) * φ x := by
  let χ := Classical.choice (CuspParameters.exists_cuspWeightCutoffs hp)
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := CuspParameters.core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential := by
    intro coupling
    exact magnetic_realization p.b coupling p.potential
      (CuspParameters.admissiblePotential hp).smooth
      (CuspParameters.admissiblePotential hp).bounded
  obtain ⟨_, _, _, κ₀, hκ₀, C, hC, threshold, hthreshold, hstates⟩ :=
    CuspParameters.exists_atomicGround_fine_weighted_decomposition_of_radialData
      hp hRad hAcore hApot χ hβ₁ hβ₁β
  exact ⟨χ, κ₀, hκ₀, C, hC, threshold, hthreshold, hstates⟩

/-- Auxiliary conditional variational assembly using only classical admission
A003. The original analytic data must still be constructed. -/
theorem thm_main_variational_from_analytic_data (h : FixedAnalyticData) : MainTheorem :=
  thm_main_of_analytic_data h (fun _ _ hCoupling hE =>
    free_landau_resolvent_kernel h.basic.b_pos hCoupling hE)

/-- Auxiliary conditional operator assembly using classical admissions A002
and A003; the original analytic data must be supplied by a proof. -/
theorem thm_main_from_analytic_data (h : FixedAnalyticData) : ConstructedPotentialMainTheorem := by
  apply constructed_main_of_analytic_data h
  · exact fun _ _ hCoupling hE => free_landau_resolvent_kernel h.basic.b_pos hCoupling hE
  · intro coupling
    exact magnetic_realization h.parameters.b coupling _ h.admissible.smooth h.admissible.bounded
  · intro L coupling
    exact magnetic_realization h.parameters.b coupling _
      (h.admissible.doubleWell_smooth L) (h.admissible.doubleWell_bounded L)

/-- The core-plus-two-cusps potential of TeX `eq:final-v` satisfies all three
items of `thm:main` whenever its fixed parameters meet `BasicConditions`.
The result chooses `L₀ > p.R` before requiring the conclusion for every
`L ≥ L₀`; the coupling sequences are then allowed to depend on L.

This is the construction theorem used to discharge the elementary
witness. Its only premise concerns the explicit scalars and cutoffs.
The spectral properties, source estimates, oscillatory hopping asymptotic
and relative Schur errors needed for the final conclusion are constructed
in the imported proofs. Here A002--A005 supply their four classical
interfaces: operator realization, free Landau resolvent, radial-core
harmonic data, and the interior elliptic estimate. -/
theorem CuspParameters.mainConclusion {p : CuspParameters} (hp : p.BasicConditions) :
    ∃ L₀ : ℝ, p.R < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → OperatorMainConclusion p.b p.potential L := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hv := CuspParameters.admissiblePotential hp
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (CuspParameters.core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    obtain ⟨hl, hr⟩ := CuspParameters.core_range p x
    exact abs_le.mpr ⟨hl, hr.trans (by norm_num)⟩
  have hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential :=
    fun coupling => magnetic_realization p.b coupling p.potential hv.smooth hv.bounded
  obtain ⟨C, hC⟩ := hv.bounded
  have hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)) := by
    intro coupling L
    exact magnetic_realization p.b coupling _
      (hv.smooth.comp (contDiff_id.add contDiff_const))
      ⟨C, fun x => hC (x + displacement L)⟩
  have hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)) := by
    intro coupling L
    exact magnetic_realization p.b coupling _
      (hv.smooth.comp (contDiff_const.sub contDiff_id))
      ⟨C, fun x => hC (displacement L - x)⟩
  have hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L) := by
    intro coupling L
    exact magnetic_realization p.b coupling _ (hv.doubleWell_smooth L) (hv.doubleWell_bounded L)
  exact CuspParameters.exists_main_separation_of_radialData classical_elliptic_interior_estimate
    hp hRad hAcore hApot hAleft hAright hAdouble
    (fun _ _ hc hE => free_landau_resolvent_kernel hp.b_pos hc hE)

/-- The active TeX `thm:main` for one literally specified potential, a
stronger statement than merely asserting that some suitable v exists.
Set `p = CuspParameters.elementaryParameters`: its values are
`r₀ = 1`, `R = 16`, `b = 1`, `ε = 1/16`, `a = β = tStar = s₀ = 1`,
and `t₀ = 1/100`, with the two fixed smooth cutoffs documented in
`ConstructionParameters.lean`. The potential is exactly the radial core
plus the two reflected log-flat cusps in `CuspParameters.potential`
(TeX `eq:explicit-core`, `eq:cusp-def`, `eq:final-v`).

The first conjunct proves its admissibility: smoothness, compact support,
range `[-1,0]` and nonradiality. Its unique nondegenerate minimum at zero
is proved separately in `ConstructionMinimum.lean`; it is not a field of
`AdmissiblePotential`. The second conjunct chooses `L₀ > 16` and proves the
three conclusions for every
fixed `L ≥ L₀`: infinitely many lowest-level crossings, infinitely many
complex hopping zeros, and alternating simple ground-state parities.
At every sufficiently large crossing the actual L² ground space is exactly
two-dimensional with both parities and a positive gap above it.

Neither the potential nor b depends on L or λ; the exceptional sequences
may depend on L. There are no hypotheses in this theorem's type. Its proof
uses the four classical admissions A002--A005 documented at `thm_main`. -/
theorem elementaryPotential_main :
    AdmissiblePotential CuspParameters.elementaryParameters.potential ∧
      ∃ L₀ : ℝ, CuspParameters.elementaryParameters.R < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
        OperatorMainConclusion CuspParameters.elementaryParameters.b
          CuspParameters.elementaryParameters.potential L := by
  exact ⟨CuspParameters.admissiblePotential CuspParameters.elementaryParameters_basicConditions,
    CuspParameters.mainConclusion CuspParameters.elementaryParameters_basicConditions⟩

/-- Formal counterpart of the three items in the active, uncommented
`thm:main` of `Infinite_Zero_Tunneling_Lean_oriented_V2.tex`.

There is one fixed smooth compactly supported nonradial potential
`v : ℝ² → [-1,0]`, one `b > 0` and one `L₀ > 0`, such that for every
fixed `L ≥ L₀` the Hamiltonian of `eq:double-well-unscaled` has:
* (i) infinitely many exact crossings of its two lowest levels tending to
  infinite coupling, with a two-dimensional ground eigenspace containing
  one even and one odd mode at every sufficiently large crossing;
* (ii) infinitely many zeros tending to infinity of the complex hopping
  coefficient `ρ_λ` from `eq:rho-intro`;
* (iii) interlaced couplings tending to infinity with simple even and simple
  odd ground states, expressing infinitely many changes of parity.

For review, unfold `ConstructedPotentialMainTheorem`, then
`OperatorMainConclusion` and `MainConclusion`. The type requires the
explicit core-plus-cusps construction, and the proof selects
`CuspParameters.elementaryParameters`. The theorem `elementaryPotential_main`
just above states the stronger fixed-witness result directly. Parameters
and cutoffs are chosen before L₀, L and λ; neither spectral data nor
tunneling estimates are premises of the final theorem.

The first two energies are implemented by variational infimum/min-max,
then identified with the actual low eigenmodes. Operator realization,
exact ground-space dimension and a gap above it supply the lowest-doublet
meaning; a full enumeration of the discrete spectrum is not constructed.
Zero spacing and differentiated asymptotic remainders, discussed elsewhere
in the introduction but absent from the boxed `thm:main`, are not part of
this result. See `docs/STATEMENT_AUDIT.md` for the detailed comparison.

This theorem has no hypotheses and no direct `sorry`. Its proof still
depends on exactly four admitted classical results: A002
`magnetic_realization`, A003 `free_landau_resolvent_kernel`, A004
`radial_core_spectral_data`, and A005
`classical_elliptic_interior_estimate`. Their precise statements, references
and natural-language proofs are recorded in `docs/ADMISSIONS.md` and its
linked documents. Thus "unconditional" refers to the theorem's statement,
not to elimination of these admitted dependencies. -/
theorem thm_main : ConstructedPotentialMainTheorem := by
  exact ⟨CuspParameters.elementaryParameters, CuspParameters.elementaryParameters_basicConditions,
    elementaryPotential_main.1, elementaryPotential_main.2⟩

end InfiniteZero
