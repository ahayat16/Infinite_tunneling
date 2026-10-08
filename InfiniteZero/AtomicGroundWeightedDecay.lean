import InfiniteZero.AtomicGroundWeightedResponse
import InfiniteZero.AtomicWeightedResidual
import InfiniteZero.SchurNormalizationThreshold

/-!
# Decay and normalization of the same genuine weighted atomic response

The exact weighted response bound is applied to the actual cusp residual.
The reference and full ground state are chosen before the weight strength.
The positive normalization stays in [1/2,1]. This is absolute exponential
decay; the finer log-flat and action-dependent forcing estimates remain separate.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1600000

theorem exists_atomicGround_weighted_decay_and_response_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ C > 0, ∃ d > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ s : AtomicSchurReference p hp coupling (hRad.gap / 2 * coupling),
      IsPositiveRadial s.coreState ∧
      ∃ q : QuantitativeSchurGroundCertificate
          (magneticOperator p.b coupling p.potential) s.vector
          (atomicGroundEnergy p.b p.potential coupling) (hRad.gap / 2 * coupling),
        (schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space)) ∈
          Icc (1 / 2) 1) ∧
        ∀ κ ∈ Icc 0 κ₀,
          ‖atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
              (q.normalizedCorrection : L2Space)‖ ≤ C * Real.exp (-d * coupling) ∧
          (let W := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
           let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
           ‖W (q.normalizedCorrection : L2Space)‖ ≤
             (12 * c * coupling / hRad.gap) *
               ‖W (atomicPerturbationMul hp (s.vector : L2Space))‖) := by
  have hg : 0 < hRad.gap := hRad.gap_pos
  obtain ⟨M, hM, hT, κr, hκr, Nr, hNr, hresponse⟩ :=
    exists_atomicGround_weighted_response_of_radialData hp hRad hAcore hApot χ
  obtain ⟨κw, hκw, d, hd, K, hK, Nw, hNw, hresidual⟩ :=
    exists_atomicWeightedResidual_decay_of_radialData hp hRad hAcore hApot
      χ.weight χ.weight_continuous hM.le hT
  obtain ⟨Nn, hNn, hnormal⟩ := exists_schurNormalization_exponential_threshold
    (H := L2Space) (show 0 ≤ 2 * K / hRad.gap by positivity) hd
  refine ⟨M, hM, hT, min κr κw, lt_min hκr hκw,
    12 * K / hRad.gap, by positivity, d, hd,
    max Nr (max Nw Nn), hNr.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcr : Nr ≤ coupling := (le_max_left _ _).trans hc
  have hcw : Nw ≤ coupling :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcn : Nn ≤ coupling :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hcpos : 0 < coupling := hNr.trans_le hcr
  obtain ⟨s, hpos, q, hq⟩ := hresponse coupling hcr
  let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
  have hc0 : 0 < c := schurNormalization_pos _
  have hc1 : c ≤ 1 := schurNormalization_le_one _
  have hres0 : ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp (s.vector : L2Space)‖ ≤
      K * coupling * Real.exp (-d * coupling) := by
    have hr := hresidual coupling hcw 0 ⟨le_rfl, hκw.le⟩
      s.coreState s.coreGround (s.vector : L2Space) s.represents
    simpa only [atomicExponentialWeightMul_zero, ContinuousLinearMap.id_apply] using hr
  have hcorr : ‖((q.correction : orthogonalComplement (s.vector : L2Space)) : L2Space)‖ ≤
      (2 * K / hRad.gap) * Real.exp (-d * coupling) := by
    have hbound := q.correction_norm_le.trans
      (div_le_div_of_nonneg_right (s.coupling_le.trans hres0)
        (mul_nonneg (half_pos hg).le hcpos.le))
    calc
      _ ≤ (K * coupling * Real.exp (-d * coupling)) / (hRad.gap / 2 * coupling) := hbound
      _ = _ := by field_simp
  have hhalf : (1 / 2 : ℝ) ≤ c := by
    exact (hnormal coupling hcn
      ((q.correction : orthogonalComplement (s.vector : L2Space)) : L2Space) hcorr).1
  refine ⟨s, hpos, q, ⟨hhalf, hc1⟩, ?_⟩
  intro κ hκ
  constructor
  swap
  · simpa only [q.normalizedCorrection_coe] using
      hq κ ⟨hκ.1, hκ.2.trans (min_le_left _ _)⟩
  let W := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
  have hr := hresidual coupling hcw κ ⟨hκ.1, hκ.2.trans (min_le_right _ _)⟩
    s.coreState s.coreGround (s.vector : L2Space) s.represents
  have hscaled : ‖W ((coupling ^ 2 : ℂ) • atomicPerturbationMul hp (s.vector : L2Space))‖ =
      coupling ^ 2 * ‖W (atomicPerturbationMul hp (s.vector : L2Space))‖ := by
    rw [W.map_smul, norm_smul, ← Complex.ofReal_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg coupling)]
  change ‖W ((coupling ^ 2 : ℂ) • atomicPerturbationMul hp (s.vector : L2Space))‖ ≤ _ at hr
  rw [hscaled] at hr
  have hmul := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 12 * c / (hRad.gap * coupling) by positivity)
  change ‖W (q.normalizedCorrection : L2Space)‖ ≤ _
  rw [q.normalizedCorrection_coe]
  calc
    _ ≤ (12 * c * coupling / hRad.gap) *
        ‖W (atomicPerturbationMul hp (s.vector : L2Space))‖ :=
      hq κ ⟨hκ.1, hκ.2.trans (min_le_left _ _)⟩
    _ = (12 * c / (hRad.gap * coupling)) *
        (coupling ^ 2 * ‖W (atomicPerturbationMul hp (s.vector : L2Space))‖) := by
      field_simp
    _ ≤ (12 * c / (hRad.gap * coupling)) *
        (K * coupling * Real.exp (-d * coupling)) := hmul
    _ = c * (12 * K / hRad.gap * Real.exp (-d * coupling)) := by field_simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hc1

/-- The absolute-decay interface, retaining the same states as the stronger
version that also records the exact forcing bound. -/
theorem exists_atomicGround_weighted_decay_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ C > 0, ∃ d > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ s : AtomicSchurReference p hp coupling (hRad.gap / 2 * coupling),
      IsPositiveRadial s.coreState ∧
      ∃ q : QuantitativeSchurGroundCertificate
          (magneticOperator p.b coupling p.potential) s.vector
          (atomicGroundEnergy p.b p.potential coupling) (hRad.gap / 2 * coupling),
        (schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space)) ∈
          Icc (1 / 2) 1) ∧
        ∀ κ ∈ Icc 0 κ₀,
          ‖atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
              (q.normalizedCorrection : L2Space)‖ ≤ C * Real.exp (-d * coupling) := by
  obtain ⟨M, hM, hT, κ₀, hκ₀, C, hC, d, hd, threshold, hthreshold, hstates⟩ :=
    exists_atomicGround_weighted_decay_and_response_of_radialData hp hRad hAcore hApot χ
  refine ⟨M, hM, hT, κ₀, hκ₀, C, hC, d, hd, threshold, hthreshold, ?_⟩
  intro coupling hc
  obtain ⟨s, hpos, q, hc, hq⟩ := hstates coupling hc
  exact ⟨s, hpos, q, hc, fun κ hκ => (hq κ hκ).1⟩

end InfiniteZero.CuspParameters
