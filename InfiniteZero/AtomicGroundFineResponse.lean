import InfiniteZero.AtomicGroundWeightedDecay
import InfiniteZero.AtomicCuspFineForcing
import InfiniteZero.RadialCoreEnergyBounds
import InfiniteZero.RadialCoreExteriorState

/-!
# The exact-action, log-flat weighted response of the true atomic ground state

The same positive radial core state supplies the exterior coefficient and the
Schur reference. Its true scaled energy lies in a fixed compact interval.
The fine cusp forcing bound is applied to this state and then to its actual
weighted response, retaining the normalization coefficient. Constants and
the weight are fixed before the coupling; both states precede the weight strength.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1600000

theorem exists_atomicGround_fine_weighted_response_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
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
              C * c * Γ * coupling ^ 3 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
  have hg : 0 < hRad.gap := hRad.gap_pos
  obtain ⟨M, hM, hT, κr, hκr, _, _, _, _, Nr, hNr, hresponse⟩ :=
    exists_atomicGround_weighted_decay_and_response_of_radialData hp hRad hAcore hApot χ
  obtain ⟨Cf, hCf, Nf, _hNf, hforce⟩ :=
    exists_atomic_cusp_fine_forcing_norm_coupling hp χ hβ₁ hβ₁β hT
  obtain ⟨NE, _hNE, henergy⟩ :=
    exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  refine ⟨M, hM, hT, min κr (1 / 16), lt_min hκr (by norm_num),
    12 * Cf / hRad.gap, by positivity,
    max Nr (max Nf NE), hNr.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcr : Nr ≤ coupling := (le_max_left _ _).trans hc
  have hcf : Nf ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hce : NE ≤ coupling := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hcpos : 0 < coupling := hNr.trans_le hcr
  have hE := henergy coupling hce
  obtain ⟨s, hpos, q, hnormal, hq⟩ := hresponse coupling hcr
  obtain ⟨Γ, hΓ, htail⟩ := s.coreGround.exists_pos_radialCore_kernel
    hp.b_pos hp.r₀_pos hcpos hpos (by linarith only [hE.1])
  refine ⟨s, hpos, q, hnormal, Γ, hΓ, htail, ?_⟩
  intro κ hκ c
  let W := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
  have hf := hforce coupling hcf _ hE κ ⟨hκ.1, hκ.2.trans (min_le_right _ _)⟩
    Γ hΓ.le s.coreState htail (s.vector : L2Space) s.represents
  have hc0 : 0 < c := schurNormalization_pos _
  have hcoeff : 0 ≤ 12 * c * coupling / hRad.gap := by positivity
  calc
    ‖W (q.normalizedCorrection : L2Space)‖ ≤
        (12 * c * coupling / hRad.gap) *
          ‖W (atomicPerturbationMul hp (s.vector : L2Space))‖ :=
      (hq κ ⟨hκ.1, hκ.2.trans (min_le_left _ _)⟩).2
    _ ≤ (12 * c * coupling / hRad.gap) *
        (Cf * Γ * coupling ^ 2 *
          Real.exp (-coupling * bridgeAction p.b
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
          Real.exp (-β₁ * (Real.log coupling) ^ 2)) :=
      mul_le_mul_of_nonneg_left hf hcoeff
    _ = _ := by ring

end InfiniteZero.CuspParameters
