import InfiniteZero.AtomicGroundFineResponse
import InfiniteZero.AtomicEnergyShiftForcing
import InfiniteZero.AtomicResponseDataJets
import InfiniteZero.CuspFineForcingJetCoupling
import InfiniteZero.RadialCoreWeightedJetBounds

/-!
# Fine data bounds for the same genuine atomic response

The true normalized Schur correction already has the fine weighted L²
bound. Its two actual semiclassical forcing terms now have pointwise jet
bounds on a fixed outer annulus. The energy-shift term uses a radial jet
estimate with no normalization coefficient, so exactly one Γ is retained.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1600000

theorem exists_atomicGround_fine_response_data_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    {rMax : ℝ} (hMax : p.R / 2 ≤ rMax) (n : ℕ) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ Cresponse > 0, ∃ Cdata > 0, ∃ N > 0,
      ∀ coupling : ℝ, N ≤ coupling →
      ∃ s : AtomicSchurReference p hp coupling (hRad.gap / 2 * coupling),
      IsPositiveRadial s.coreState ∧
      ∃ q : QuantitativeSchurGroundCertificate
          (magneticOperator p.b coupling p.potential) s.vector
          (atomicGroundEnergy p.b p.potential coupling) (hRad.gap / 2 * coupling),
        (schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space)) ∈
          Icc (1 / 2) 1) ∧
        ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            s.coreState x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          ∀ κ ∈ Icc 0 κ₀,
            let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
            ‖atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
                (q.normalizedCorrection : L2Space)‖ ≤
              Cresponse * c * Γ * coupling ^ 3 * Real.exp (-coupling * bridgeAction p.b
                (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2) ∧
            ∀ j : ℕ, j ≤ n → ∀ x : Plane, ‖x‖ ∈ Icc (p.R / 2) rMax →
              Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j (p.atomicScaledResponseSource coupling c s.coreState) x‖ ≤
                Cdata * c * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                  Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
  obtain ⟨M, hM, hT, κr, hκr, Cr, hCr, Nr, hNr, hstates⟩ :=
    exists_atomicGround_fine_weighted_response_of_radialData hp hRad hAcore hApot χ hβ₁ hβ₁β
  obtain ⟨κφ, hκφ, hκφ16, Cφ, hCφ, dφ, hdφ, Nφ, _hNφ, hradial⟩ :=
    exists_radialCore_weighted_jet_decay_of_radialData hp hRad hAcore χ hMax n
  obtain ⟨Cp, hCp, Np, _hNp, hpoint⟩ :=
    exists_cusp_fine_forcing_jets_pointwise_coupling hp χ hβ₁ hβ₁β n
  obtain ⟨Cf, hCf, Nf, _hNf, hforce⟩ :=
    exists_atomic_cusp_fine_forcing_norm_coupling hp χ hβ₁ hβ₁β hT
  obtain ⟨NE, _hNE, henergy⟩ :=
    exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  refine ⟨M, hM, hT, min κr κφ, lt_min hκr hκφ, Cr, hCr,
    Cp + 3 * Cf * Cφ, by positivity,
    max Nr (max Nφ (max Np (max Nf NE))), hNr.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcr : Nr ≤ coupling := (le_max_left _ _).trans hc
  have hcφ : Nφ ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcp : Np ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hcf : Nf ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hce : NE ≤ coupling := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hcpos := hNr.trans_le hcr
  have hE := henergy coupling hce
  obtain ⟨s, hpos, q, hnormal, Γ, hΓ, htail, hresponse⟩ := hstates coupling hcr
  refine ⟨s, hpos, q, hnormal, Γ, hΓ, htail, ?_⟩
  intro κ hκ c
  have hκr' : κ ∈ Icc 0 κr := ⟨hκ.1, hκ.2.trans (min_le_left _ _)⟩
  have hκφ' : κ ∈ Icc 0 κφ := ⟨hκ.1, hκ.2.trans (min_le_right _ _)⟩
  have hκ16 : κ ∈ Icc (0 : ℝ) (1 / 16) := ⟨hκ.1, hκφ'.2.trans hκφ16⟩
  have hc0 : 0 < c := schurNormalization_pos _
  refine ⟨hresponse κ hκr', ?_⟩
  let B := Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
    Real.exp (-β₁ * (Real.log coupling) ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf := hforce coupling hcf _ hE κ hκ16 Γ hΓ.le s.coreState htail
    (s.vector : L2Space) s.represents
  have hshift : |p.atomicScaledEnergyShift coupling| ≤ (3 * Cf) * B := by
    have hs := s.scaled_energy_shift_le_three_weighted_forcing q hcpos hnormal.1
      χ.weight χ.weight_continuous hT hκ.1
    exact hs.trans (by
      convert mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 3) using 1
      dsimp [B]
      ring)
  intro j hj x hx
  have hjpoint : Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
      ‖iteratedFDeriv ℝ j (fun y => (p.atomicPerturbation y : ℂ) * s.coreState y) x‖ ≤
      Cp * B := by
    convert hpoint coupling hcp _ hE κ hκ16 Γ hΓ.le s.coreState s.coreGround.1.1 htail j hj x
      using 1
    dsimp [B]
    ring
  have hjradial : Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
      ‖iteratedFDeriv ℝ j s.coreState x‖ ≤ Cφ := by
    apply (hradial coupling hcφ s.coreState s.coreGround hpos κ hκφ' x hx j hj).trans
    have he : Real.exp (-dφ * coupling) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hCφ.le
  have hdata := weighted_atomicScaledResponseSource_jet_le hp coupling hc0.le
    s.coreGround.1.1 j x χ.weight (inv_nonneg.mpr hcpos.le) hCφ.le
    (by simpa only [div_inv_eq_mul] using hjpoint)
    (by simpa only [div_inv_eq_mul] using hjradial) hshift
  simp only [div_inv_eq_mul] at hdata
  convert hdata using 1
  dsimp [B]
  ring

end InfiniteZero.CuspParameters
