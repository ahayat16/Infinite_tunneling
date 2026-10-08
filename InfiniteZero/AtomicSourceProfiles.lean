import InfiniteZero.AtomicScatteredSourceJets
import InfiniteZero.CuspIncomingSourceJets
import InfiniteZero.RadialCoreEnergyBounds

/-!
# Simultaneous profiles of the genuine incoming and scattered sources

One choice of the true radial and full atomic states supplies both source
profiles, on both closed cusp supports, for every prescribed derivative and
weight strength. The incoming, global scattered and local scattered margins
are independent. All estimates use the existing physical source definition.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- Incoming and scattered cusp profiles for the same states and coefficient.
The polynomial losses are sufficient bounds, without a leading-prefactor
asymptotic assertion. The classical interior estimate remains an input. -/
theorem exists_atomicGround_source_profiles_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {βin βglobal βlocal : ℝ}
    (hi : 0 < βin) (hiβ : βin < p.β)
    (hg : 0 < βglobal) (hgβ : βglobal < p.β)
    (hl : 0 < βlocal) (hlβ : βlocal < p.β) (n : ℕ) :
    ∃ κ₀ > 0, ∃ Cin > 0, ∃ Csc > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let A : ℝ := c * Γ *
            Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
            Real.exp (-βglobal * (Real.log coupling) ^ 2)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n →
            (∀ x ∈ tsupport p.cuspPlus,
              (coupling⁻¹) ^ j * ‖iteratedFDeriv ℝ j
                (atomicSource coupling⁻¹ p.atomicPerturbation (fun y => (c : ℂ) * φ y)) x‖ ≤
                Cin * c * Γ * coupling ^ (n + 4) *
                  logFlat βin p.tStar (p.normalCoordinate x) *
                  Real.exp (-coupling * (bridgeAction p.b
                    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
                    p.normalCoordinate x / 8))) ∧
            (∀ x ∈ tsupport p.cuspMinus,
              (coupling⁻¹) ^ j * ‖iteratedFDeriv ℝ j
                (atomicSource coupling⁻¹ p.atomicPerturbation (fun y => (c : ℂ) * φ y)) x‖ ≤
                Cin * c * Γ * coupling ^ (n + 4) *
                  logFlat βin p.tStar (p.normalCoordinate (reflection x)) *
                  Real.exp (-coupling * (bridgeAction p.b
                    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
                    p.normalCoordinate (reflection x) / 8))) ∧
            (∀ x ∈ tsupport p.cuspPlus,
              (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
                Csc * coupling ^ 6 * A * logFlat βlocal p.tStar (p.normalCoordinate x) *
                  Real.exp (-κ * coupling * p.normalCoordinate x)) ∧
            (∀ x ∈ tsupport p.cuspMinus,
              (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
                Csc * coupling ^ 6 * A *
                  logFlat βlocal p.tStar (p.normalCoordinate (reflection x)) *
                  Real.exp (-κ * coupling * p.normalCoordinate (reflection x))) := by
  obtain ⟨κ₀, hκ₀, _Cη, _hCη, Csc, hCsc, Ts, hTs, hstates⟩ :=
    exists_atomicGround_scattered_source_jets_of_radialData
      hInterior hp hRad hAcore hApot χ hg hgβ hl hlβ n
  obtain ⟨Cin, hCin, h₀, hh₀, hincoming⟩ := exists_cusp_incoming_source_jet_bound hp hi hiβ n
  obtain ⟨Te, _hTe, henergy⟩ :=
    exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  let threshold := max Ts (max Te (max 1 h₀⁻¹))
  refine ⟨κ₀, hκ₀, Cin, hCin, Csc, hCsc, threshold,
    hTs.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hthresholds : Ts ≤ coupling ∧ Te ≤ coupling ∧ 1 ≤ coupling ∧ h₀⁻¹ ≤ coupling := by
    simpa only [threshold, max_le_iff] using hc
  obtain ⟨hcs, hce, hc1, hch⟩ := hthresholds
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  have hsmall : coupling⁻¹ ≤ h₀ := (inv_le_comm₀ hcpos hh₀).mpr hch
  have hE := henergy coupling hce
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, _hfsmooth, horth, _heq, hprofiles⟩ := hstates coupling hcs
  have hc0 : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hcRange.1
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, horth, ?_⟩
  intro κ hκ j hj
  obtain ⟨_hηjets, hsp, hsm⟩ := hprofiles κ hκ j hj
  obtain ⟨hip, him⟩ := hincoming _ hE coupling⁻¹ (inv_pos.mpr hcpos) hsmall
    c hc0 Γ hΓ.le φ hφ.1.1 htail j hj
  have hexp (a : ℝ) : -a / coupling⁻¹ = -coupling * a := by
    rw [div_inv_eq_mul]
    ring
  refine ⟨?_, ?_, hsp, hsm⟩
  · intro x hx
    simpa only [inv_pow, inv_inv, hexp] using hip x hx
  · intro x hx
    simpa only [inv_pow, inv_inv, hexp] using him x hx

end InfiniteZero.CuspParameters
