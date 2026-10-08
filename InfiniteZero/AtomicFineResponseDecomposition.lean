import InfiniteZero.AtomicFineResponseData
import InfiniteZero.AtomicScaledResponseEquation
import InfiniteZero.WeightedWavefunctionL2
import InfiniteZero.LocalWeightedJetBounds
import InfiniteZero.CuspPacketNeighborhood

/-!
# The genuine response equation with fine local data norms

The same positive radial core state, full ground state, normalization and
exterior coefficient satisfy the exact semiclassical response equation.
The correction has its fine global weighted mass bound. Every fixed finite
family of derivatives of the complete two-term source has a fine local L²
bound on the fixed cusp neighborhood. No derivative of the weight or of
the indicator is taken, and no pointwise estimate for the correction is
asserted. All states and coefficients precede the weight strength.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1600000

theorem exists_atomicGround_fine_response_decomposition_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    (n : ℕ) :
    ∃ M > 0, ∃ _hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ Cresponse > 0, ∃ CdataL2 > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let f : Wavefunction := p.atomicScaledResponseSource coupling c φ
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ ContDiff ℝ ∞ f ∧
          waveInner φ η = 0 ∧
          (∀ κ ∈ Icc 0 κ₀,
            mass (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * η x) ≤
              (Cresponse * c * Γ * coupling ^ 3 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2) ∧
          (∀ x : Plane,
            (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
              (magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) = f x) ∧
          (∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n → ∀ v : Fin j → Plane,
            (∀ i, ‖v i‖ ≤ 1) →
            MemLp (p.cuspPacketNeighborhood.indicator
              (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) 2 volume ∧
            mass (p.cuspPacketNeighborhood.indicator
              (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) ≤
              (CdataL2 * c * Γ * coupling ^ 2 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2) ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ (ι : Type*) [Fintype ι] (orders : ι → ℕ),
            (∀ i, orders i ≤ n) → ∀ v : (i : ι) → Fin (orders i) → Plane,
            (∀ i j, ‖v i j‖ ≤ 1) →
            ∃ hF : ∀ i, MemLp (p.cuspPacketNeighborhood.indicator
                (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f (orders i) (v i))) 2 volume,
              (∑ i, ‖(hF i).toLp (p.cuspPacketNeighborhood.indicator
                (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f (orders i) (v i)))‖) ≤
                (Fintype.card ι : ℝ) * CdataL2 * c * Γ * coupling ^ 2 *
                  Real.exp (-coupling * bridgeAction p.b
                    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                  Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
  obtain ⟨M, hM, hT, κ₀, hκ₀, Cr, hCr, Cd, hCd, threshold, hthreshold, hstates⟩ :=
    exists_atomicGround_fine_response_data_of_radialData hp hRad hAcore hApot χ hβ₁ hβ₁β
      (half_radius_le_cuspPacketRadius hp) n
  have hRadius := cuspPacketRadius_pos hp
  refine ⟨M, hM, hT, κ₀, hκ₀, Cr, hCr,
    Real.sqrt Real.pi * p.cuspPacketRadius * Cd, by positivity,
    threshold, hthreshold, ?_⟩
  intro coupling hc
  have hcpos : 0 < coupling := hthreshold.trans_le hc
  obtain ⟨s, hpos, q, hnormal, Γ, hΓ, htail, hresponse⟩ := hstates coupling hc
  obtain ⟨ψ, hψ, _, hηsmooth, hηLp, hηrep, hηeq⟩ :=
    s.exists_scaled_responseWavefunction q (hApot coupling) hcpos
  let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
  have hc0 : 0 < c := schurNormalization_pos _
  let f : Wavefunction := p.atomicScaledResponseSource coupling c s.coreState
  have hf : ContDiff ℝ ∞ f :=
    atomicScaledResponseSource_contDiff hp coupling c s.coreGround.1.1
  let Bd : ℝ := (Real.sqrt Real.pi * p.cuspPacketRadius * Cd) * c * Γ * coupling ^ 2 *
    Real.exp (-coupling * bridgeAction p.b
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
    Real.exp (-β₁ * (Real.log coupling) ^ 2)
  have hBd : 0 ≤ Bd := by dsimp [Bd]; positivity
  have hlocal (κ : ℝ) (hκ : κ ∈ Icc 0 κ₀) (j : ℕ) (hj : j ≤ n)
      (v : Fin j → Plane) (hv : ∀ i, ‖v i‖ ≤ 1) :
      MemLp (p.cuspPacketNeighborhood.indicator
        (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) 2 volume ∧
      mass (p.cuspPacketNeighborhood.indicator
        (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) ≤ Bd ^ 2 := by
    let B : ℝ := Cd * c * Γ * coupling ^ 2 *
      Real.exp (-coupling * bridgeAction p.b
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
      Real.exp (-β₁ * (Real.log coupling) ^ 2)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hpoint (x : Plane) (hx : x ∈ p.cuspPacketNeighborhood) :
        Real.exp (κ / coupling⁻¹ * χ.weight x) * (coupling⁻¹) ^ j *
          ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
      simpa only [div_inv_eq_mul, f, B] using
        (hresponse κ hκ).2 j hj x (cuspPacketNeighborhood_norm_bounds p hx)
    have hbound := memLp_mass_indicator_weightedSemiclassicalJet
      χ.weight_continuous hf (isOpen_cuspPacketNeighborhood p).measurableSet hRadius.le
      (cuspPacketNeighborhood_subset_closedBall p) (inv_nonneg.mpr hcpos.le)
      hB j v hv hpoint
    refine ⟨hbound.1, hbound.2.trans_eq ?_⟩
    dsimp [Bd, B]
    ring
  refine ⟨s.coreState, ψ, s.coreGround, hpos, hψ, c, hnormal, Γ, hΓ, htail,
    hηsmooth, hηLp, hf, ?_, ?_, hηeq, hlocal, ?_⟩
  · have horth := q.normalizedCorrection_orthogonal s.vector_norm
    rwa [s.represents.inner_eq_waveInner hηrep] at horth
  · intro κ hκ
    rw [hηrep.mass_atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ]
    exact pow_le_pow_left₀ (norm_nonneg _) (hresponse κ hκ).1 2
  · intro κ hκ ι _ orders horders v hv
    have hi (i : ι) := hlocal κ hκ (orders i) (horders i) (v i) (hv i)
    refine ⟨fun i => (hi i).1, ?_⟩
    calc
      _ ≤ (Fintype.card ι : ℝ) * Bd := sum_norm_toLp_le_card_mul_of_mass_le_sq
        (fun i => p.cuspPacketNeighborhood.indicator
          (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f (orders i) (v i)))
        (fun i => (hi i).1) hBd (fun i => (hi i).2)
      _ = _ := by dsimp [Bd]; ring

end InfiniteZero.CuspParameters
