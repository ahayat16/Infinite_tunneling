import InfiniteZero.AtomicSourceL1
import InfiniteZero.ActiveSourcePairingL1Bounds
import InfiniteZero.AtomicGroundEnergyBounds

/-!
# Actual scattered contributions in an active cusp cell

The incoming and scattered states are the same orthogonal decomposition
provided by the atomic estimates. Mixed pairings retain three logarithmic
margins, and the scattered/scattered pairing retains four. The bridge uses
the full atomic energy while the two radial actions use the core energy.
No action loss is spent in the bridge estimate.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

theorem exists_atomicGround_active_scattered_bounds_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {L β₀ : ℝ} (hL : p.R < 2 * L)
    (hβ₀ : 0 < β₀) (hβ₀β : β₀ < p.β) :
    ∃ Cmix > 0, ∃ Css > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          scaledAtomicEnergy p coupling ∈ Icc (1 / 2 : ℝ) 1 ∧
          let u : Wavefunction := fun x => (c : ℂ) * φ x
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let Q := fun f g : Wavefunction =>
            sourcePairing coupling⁻¹ (sourceKernel p.b L coupling⁻¹
              (scaledAtomicEnergy p coupling))
              (componentSource p coupling⁻¹ f 1) (componentSource p coupling⁻¹ g 2)
          let B := c ^ 2 * Γ ^ 2 * Real.exp (-coupling *
            (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))))
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          ‖Q u η‖ ≤ Cmix * B * coupling ^ 10 *
            Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2) ∧
          ‖Q η u‖ ≤ Cmix * B * coupling ^ 10 *
            Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2) ∧
          ‖Q η η‖ ≤ Css * B * coupling ^ 12 *
            Real.exp (-(4 * β₀) * (Real.log coupling) ^ 2) := by
  obtain ⟨Ci, hCi, Cs, hCs, Ts, _hTs, hstates⟩ :=
    exists_atomicGround_source_L1_of_radialData
      hInterior hp hRad hAcore hApot χ hβ₀ hβ₀β hβ₀ hβ₀β hβ₀ hβ₀β
  obtain ⟨Te, _hTe, henergy⟩ :=
    exists_scaledAtomicEnergy_pos_of_radialData hp hRad hAcore hApot
  obtain ⟨K, hK, hpair⟩ := exists_activeSourcePairing_L1_bound hp hL
  let threshold := max Ts (max Te 1)
  refine ⟨K * Ci * Cs, by positivity, K * Cs * Cs, by positivity,
    threshold, zero_lt_one.trans_le ((le_max_right _ _).trans (le_max_right _ _)), ?_⟩
  intro coupling hc
  have hthresholds : Ts ≤ coupling ∧ Te ≤ coupling ∧ 1 ≤ coupling := by
    simpa only [threshold, max_le_iff] using hc
  obtain ⟨hcTs, hcTe, hc1⟩ := hthresholds
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, horth, hsource⟩ := hstates coupling hcTs
  have hE := henergy coupling hcTe
  have hEbox : scaledAtomicEnergy p coupling ∈ Icc (1 / 2 : ℝ) 1 :=
    ⟨hE.1, hE.2.2⟩
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hcRange.1
  let u : Wavefunction := fun x => (c : ℂ) * φ x
  let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
  obtain ⟨hi₁, hs₁, hbi₁, hbs₁⟩ := hsource 1 (Or.inl rfl)
  obtain ⟨hi₂, hs₂, hbi₂, hbs₂⟩ := hsource 2 (Or.inr rfl)
  have hsupport (f g : Wavefunction) :
      (Function.support (componentSource p coupling⁻¹ f 1) ⊆ tsupport p.cuspPlus ∧
        Function.support (componentSource p coupling⁻¹ g 2) ⊆ tsupport p.cuspMinus) ∨
      (Function.support (componentSource p coupling⁻¹ f 1) ⊆ tsupport p.cuspMinus ∧
        Function.support (componentSource p coupling⁻¹ g 2) ⊆ tsupport p.cuspPlus) := by
    exact Or.inl ⟨(componentSource_plus_support_subset p coupling⁻¹ f).trans
      (subset_closure), (componentSource_minus_support_subset p coupling⁻¹ g).trans
      (subset_closure)⟩
  have hmix₁ := hpair coupling hc1 _ hEbox
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
    c Γ Ci Cs β₀ (β₀ + β₀) hcpos.le hΓ.le hCi.le hCs.le 4 6
    _ _ hi₁ hs₂ (hsupport u η) hbi₁ hbs₂
  have hmix₂ := hpair coupling hc1 _ hEbox
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
    c Γ Cs Ci (β₀ + β₀) β₀ hcpos.le hΓ.le hCs.le hCi.le 6 4
    _ _ hs₁ hi₂ (hsupport η u) hbs₁ hbi₂
  have hss := hpair coupling hc1 _ hEbox
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
    c Γ Cs Cs (β₀ + β₀) (β₀ + β₀) hcpos.le hΓ.le hCs.le hCs.le 6 6
    _ _ hs₁ hs₂ (hsupport η η) hbs₁ hbs₂
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail, hEbox,
    hηsmooth, hηLp, horth, ?_, ?_, ?_⟩
  · convert hmix₁ using 1
    ring_nf
  · convert hmix₂ using 1
    ring_nf
  · convert hss using 1
    ring_nf

end InfiniteZero.CuspParameters
