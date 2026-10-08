import InfiniteZero.AtomicCuspWeightedInverse
import InfiniteZero.AtomicGroundComparison
import InfiniteZero.WeightedSchurCorrection
import InfiniteZero.SchurResponseEquation

/-!
# Weighted response of the genuine atomic ground state

The reference, its compressed inverse and the quantitative ground-state
certificate are constructed together. The weighted correction is controlled
by the actual weighted cusp forcing, retaining the positive normalization
coefficient. No estimate of that forcing or of a scattered source is assumed.
-/

noncomputable section
open Set

namespace InfiniteZero

theorem AtomicSchurReference.residual_equation {p : CuspParameters}
    {hp : p.BasicConditions} {coupling gap : ℝ}
    (s : AtomicSchurReference p hp coupling gap)
    (hAcore : IsMagneticRealization p.b coupling p.core)
    (hApot : IsMagneticRealization p.b coupling p.potential) :
    magneticOperator p.b coupling p.potential s.vector =
      (atomicGroundEnergy p.b p.core coupling : ℂ) • (s.vector : L2Space) +
        (coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp (s.vector : L2Space) := by
  have heig : (s.vector : L2Space) ∈ operatorEigenspace
      (magneticOperator p.b coupling p.core) (atomicGroundEnergy p.b p.core coupling) :=
    (hAcore.eigenfunction_iff _ _).mpr ⟨s.coreState, s.coreGround.1, s.represents⟩
  obtain ⟨v, hv, hAv⟩ := (magneticOperator p.b coupling p.potential).mem_graph_iff.mp
    (CuspParameters.atomicOperator_graph_of_core_eigenvector hp coupling hAcore hApot heig)
  have hv' : v = s.vector := Subtype.ext hv
  simpa only [hv'] using hAv

namespace CuspParameters

set_option maxHeartbeats 1600000

/-- The same genuine normalized ground vector has a weighted response
bounded by its concrete cusp forcing. All uniform constants precede the
coupling; the state and its normalization precede the weight strength. -/
theorem exists_atomicGround_weighted_response_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ threshold > 0, ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ s : AtomicSchurReference p hp coupling (hRad.gap / 2 * coupling),
      IsPositiveRadial s.coreState ∧
      ∃ q : QuantitativeSchurGroundCertificate
          (magneticOperator p.b coupling p.potential) s.vector
          (atomicGroundEnergy p.b p.potential coupling) (hRad.gap / 2 * coupling),
        ∀ κ ∈ Icc 0 κ₀,
          let W := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
          let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
          ‖W ((q.certificate.normalizedVector : L2Space) - (c : ℂ) • (s.vector : L2Space))‖ ≤
            (12 * c * coupling / hRad.gap) *
              ‖W (atomicPerturbationMul hp (s.vector : L2Space))‖ := by
  obtain ⟨M, hM, hT, κ₀, hκ₀, threshold, hthreshold, hreference⟩ :=
    exists_atomic_cusp_weighted_reference_of_radialData hp hRad hAcore hApot χ
  refine ⟨M, hM, hT, κ₀, hκ₀, threshold, hthreshold, ?_⟩
  intro coupling hc
  have hcpos : 0 < coupling := hthreshold.trans_le hc
  obtain ⟨s, hpos, hresolvent⟩ := hreference coupling hc
  obtain ⟨q, _, hE, _⟩ :=
    s.exists_ground_comparison (mul_pos (half_pos hRad.gap_pos) hcpos) (hApot coupling)
  have hE' : atomicGroundEnergy p.b p.potential coupling ≤
      atomicGroundEnergy p.b p.core coupling := sub_nonneg.mp hE
  obtain ⟨R, hR, hRbound⟩ := hresolvent _ hE'
  refine ⟨s, hpos, q, ?_⟩
  intro κ hκ W c
  let Wm := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling (-κ)
  let r := (coupling ^ 2 : ℂ) • atomicPerturbationMul hp (s.vector : L2Space)
  have hresponse := q.norm_weighted_normalizedVector_sub_smul_le
    (hApot coupling).selfAdjoint s.vector_norm R hR
    (atomicGroundEnergy p.b p.core coupling) r
    (s.residual_equation (hAcore coupling) (hApot coupling)) W Wm
    (atomicExponentialWeightMul_neg_cancel_left χ.weight χ.weight_continuous hT coupling κ)
  have hscaled : ‖W r‖ = coupling ^ 2 *
      ‖W (atomicPerturbationMul hp (s.vector : L2Space))‖ := by
    rw [show W r = (coupling ^ 2 : ℂ) •
      W (atomicPerturbationMul hp (s.vector : L2Space)) from W.map_smul _ _]
    rw [norm_smul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg coupling)]
  calc
    _ ≤ c * ‖weightedProjectedResolvent (s.vector : L2Space) W Wm R‖ * ‖W r‖ := hresponse
    _ ≤ c * (12 / (hRad.gap * coupling)) * ‖W r‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hRbound κ hκ) (schurNormalization_pos _).le)
        (norm_nonneg _)
    _ = _ := by rw [hscaled]; field_simp

end CuspParameters
end InfiniteZero
