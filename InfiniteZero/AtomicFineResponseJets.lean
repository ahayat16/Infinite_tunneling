import InfiniteZero.AtomicFineResponseDecomposition
import InfiniteZero.AtomicGroundEnergyBounds
import InfiniteZero.WeightedMagneticInteriorEstimate

/-!
# Fine weighted jets of the actual atomic correction

The positive radial state, the full ground state, their normalization and
their exterior coefficient are chosen once, before the weight strength,
derivative order and evaluation point. The fixed-ball interior estimate is
an explicit classical input; the magnetic rescaling and all source estimates
are supplied by proved results. The pointwise bound is local to the closed
inner cusp neighborhood, and retains the exact core action and log-flat loss.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1600000

theorem exists_atomicGround_fine_response_jets_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    (n : ℕ) :
    ∃ κ₀ > 0, ∃ C > 0, ∃ threshold > 0,
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
          (∀ x : Plane,
            (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
              (magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) = f x) ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n →
            ∀ x ∈ closure p.cuspPacketInnerNeighborhood,
              Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j η x‖ ≤
                C * c * Γ * coupling ^ 4 *
                  Real.exp (-coupling * bridgeAction p.b
                    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                  Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
  obtain ⟨M, _hM, hT, κ₀, hκ₀, Cr, hCr, Cd, hCd, Td, hTd, hstates⟩ :=
    exists_atomicGround_fine_response_decomposition_of_radialData.{0}
      hp hRad hAcore hApot χ hβ₁ hβ₁β n
  obtain ⟨Ce, hCe, hinterior⟩ :=
    exists_cusp_weighted_magnetic_interior_jet_bound hInterior hp χ n κ₀ hκ₀.le
  obtain ⟨Te, _hTe, henergy⟩ :=
    exists_scaledAtomicEnergy_pos_of_radialData hp hRad hAcore hApot
  let threshold := max Td (max Te (max 1 p.cuspPacketBallScale⁻¹))
  have hthreshold : 0 < threshold := hTd.trans_le (le_max_left _ _)
  refine ⟨κ₀, hκ₀, Ce * (Cr + Cd), mul_pos hCe (add_pos hCr hCd),
    threshold, hthreshold, ?_⟩
  intro coupling hc
  have hthresholds : Td ≤ coupling ∧ Te ≤ coupling ∧ 1 ≤ coupling ∧
      p.cuspPacketBallScale⁻¹ ≤ coupling := by
    simpa only [threshold, max_le_iff] using hc
  obtain ⟨hcd, hce, hc1, hcs⟩ := hthresholds
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  have hsmall : coupling⁻¹ ≤ p.cuspPacketBallScale :=
    (inv_le_comm₀ hcpos (cuspPacketBallScale_pos hp)).mpr hcs
  obtain ⟨_, hepos, heupper⟩ := henergy coupling hce
  have heScaled : scaledAtomicEnergy p coupling =
      -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.potential coupling) := by
    unfold scaledAtomicEnergy
    ring
  rw [heScaled] at hepos heupper
  have heAbs : |(coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.potential coupling| ≤ 1 := by
    rw [abs_of_nonpos (by linarith)]
    exact heupper
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, hfsmooth, horth, hmass, heq, hdata, _⟩ := hstates coupling hcd
  let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
  let f : Wavefunction := p.atomicScaledResponseSource coupling c φ
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hcRange.1
  let G : ℝ := c * Γ *
    Real.exp (-coupling * bridgeAction p.b
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
    Real.exp (-β₁ * (Real.log coupling) ^ 2)
  have hG : 0 < G := by dsimp [G]; positivity
  let U := Cr * G * coupling ^ 3
  let F := Cd * G * coupling ^ 2
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, hfsmooth, horth, heq, ?_⟩
  intro κ hκ j hj x hx
  have hweighted : MemLp
      (fun y => (Real.exp (κ * coupling * χ.weight y) : ℂ) * η y) 2 volume :=
    ((represents_toLp hηLp).atomicExponentialWeightMul
      χ.weight χ.weight_continuous hT coupling κ).memLp
  have huMass : MemLp
      (fun y => (Real.exp (κ * coupling * χ.weight y) : ℂ) * η y) 2 volume ∧
      mass (fun y => (Real.exp (κ * coupling * χ.weight y) : ℂ) * η y) ≤ U ^ 2 := by
    refine ⟨hweighted, ?_⟩
    convert hmass κ hκ using 1
    dsimp [U, G]
    ring
  have hfMass : ∀ k : ℕ, k ≤ n → ∀ v : Fin k → Plane, (∀ i, ‖v i‖ ≤ 1) →
      MemLp (p.cuspPacketNeighborhood.indicator
        (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f k v)) 2 volume ∧
      mass (p.cuspPacketNeighborhood.indicator
        (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f k v)) ≤ F ^ 2 := by
    intro k hk v hv
    refine ⟨(hdata κ hκ k hk v hv).1, ?_⟩
    convert (hdata κ hκ k hk v hv).2 using 1
    dsimp [F, G]
    ring
  have hjet := hinterior coupling hc1 (atomicGroundEnergy p.b p.potential coupling)
    heAbs x hx hsmall η f hηsmooth hfsmooth heq κ hκ U F hU hF huMass hfMass j hj
  have hpow : coupling ^ 2 ≤ coupling ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg coupling) (sub_nonneg.mpr hc1)]
  have hsum : U + F ≤ (Cr + Cd) * G * coupling ^ 3 := by
    have hFle := mul_le_mul_of_nonneg_left hpow (mul_pos hCd hG).le
    dsimp [U, F]
    nlinarith
  calc
    _ ≤ Ce * coupling * (U + F) := hjet
    _ ≤ Ce * coupling * ((Cr + Cd) * G * coupling ^ 3) :=
      mul_le_mul_of_nonneg_left hsum (mul_pos hCe hcpos).le
    _ = _ := by dsimp [G]; ring

end InfiniteZero.CuspParameters
