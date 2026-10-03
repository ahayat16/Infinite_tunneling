import InfiniteZero.AtomicCuspWeightedGraph
import InfiniteZero.AtomicExponentialWeightOps
import InfiniteZero.AtomicResidualDecay
import InfiniteZero.WeightedCompressedEstimate
import InfiniteZero.WeightedProjectedResolvent
import InfiniteZero.WeightedResidualAbsorption
import InfiniteZero.AtomicSchurReference

/-!
# Weighted inverse for the actual cusp weight and atomic compression

The reference ground state is constructed before the energy and weight
strength. Its compression is self-adjoint and coercive. The exact weighted
graph bound, exterior decay and true cusp residual imply the conjugated
inverse estimate, including the projection, uniformly below the core energy.
-/

noncomputable section
open Set
namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 800000

/-- The below-core-energy version of LA.2, on the genuine atomic operator
in the non-rescaled convention. This includes the actual full ground energy;
the portion of the manuscript's window above the core energy is not claimed.
The inverse and all bounds are constructed from radial data and realizations;
no weighted inverse or nonradial source estimate is an input. -/
theorem exists_atomic_cusp_weighted_reference_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ threshold > 0, ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ s : AtomicSchurReference p hp coupling (hRad.gap / 2 * coupling),
        IsPositiveRadial s.coreState ∧
        ∀ E : ℝ, E ≤ atomicGroundEnergy p.b p.core coupling →
        ∃ R : orthogonalComplement (s.vector : L2Space) →L[ℂ]
            orthogonalComplement (s.vector : L2Space),
          IsOperatorResolvent (orthogonalCompression
            (magneticOperator p.b coupling p.potential) (s.vector : L2Space)) E R ∧
          ∀ κ ∈ Icc 0 κ₀,
            ‖weightedProjectedResolvent (s.vector : L2Space)
              (atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ)
              (atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling (-κ)) R‖ ≤
                12 / (hRad.gap * coupling) := by
  obtain ⟨M, hM, hT, κg, hκg, Ng, hNg, hgraph⟩ :=
    exists_atomic_cusp_weighted_graph_lower_of_radialData hp hRad hAcore hApot χ
  obtain ⟨κt, hκt, c, hc, C, hC, Nt, hNt, htail⟩ :=
    exists_atomicWeightedTail_of_radialData hp hRad hAcore hApot χ.weight
      χ.weight_continuous hM.le hT (fun _ hx => χ.weight_zero_on_core hx)
  obtain ⟨K, hK, d, hd, Nr, hNr, hresidual⟩ :=
    exists_atomicResidual_decay_of_radialData hp hRad hAcore hApot
  obtain ⟨Na, hNa, habsorption⟩ :=
    exists_weighted_residual_absorption hRad.gap_pos hC.le hc hK.le hd
  refine ⟨M, hM, hT, min κg κt, lt_min hκg hκt,
    max Ng (max Nt (max Nr Na)), hNg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hcoupling
  have hcg : Ng ≤ coupling := (le_max_left _ _).trans hcoupling
  have hct : Nt ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hcoupling)
  have hcr : Nr ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hcoupling))
  have hca : Na ≤ coupling := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hcoupling))
  have hcoupling_pos : 0 < coupling := hNg.trans_le hcg
  obtain ⟨φ, hφ, hpos, hweighted⟩ := hgraph coupling hcg
  let u : L2Space := hφ.1.2.1.toLp φ
  have hu : Represents u φ := represents_toLp hφ.1.2.1
  have huEig : u ∈ operatorEigenspace (magneticOperator p.b coupling p.core)
      (atomicGroundEnergy p.b p.core coupling) :=
    ((hAcore coupling).eigenfunction_iff _ u).mpr ⟨φ, hφ.1, hu⟩
  obtain ⟨v, hv, hvA⟩ := (magneticOperator p.b coupling p.potential).mem_graph_iff.mp
    (atomicOperator_graph_of_core_eigenvector hp coupling (hAcore coupling)
      (hApot coupling) huEig)
  have hvrep : Represents (v : L2Space) φ := by simpa only [hv] using hu
  have hvnorm : ‖(v : L2Space)‖ = 1 := by
    have hs := hvrep.norm_sq_eq_mass.trans hφ.2
    nlinarith [norm_nonneg (v : L2Space)]
  let A := magneticOperator p.b coupling p.potential
  let E₀ := atomicGroundEnergy p.b p.core coupling
  let r : L2Space := (coupling ^ 2 : ℂ) • atomicPerturbationMul hp (v : L2Space)
  have hr : A v = (E₀ : ℂ) • (v : L2Space) + r := by
    simpa only [A, E₀, r, hv] using hvA
  have hbase : ∀ z : A.domain, inner ℂ (v : L2Space) (z : L2Space) = 0 →
      (E₀ + hRad.gap / 2 * coupling) * ‖(z : L2Space)‖ ^ 2 ≤
        (inner ℂ (z : L2Space) (A z)).re := by
    intro z hz
    have h := hweighted 0 ⟨le_refl _, hκg.le⟩ z
    have hz' : inner ℂ (hφ.1.2.1.toLp φ) (z : L2Space) = 0 := by
      simpa only [hv] using hz
    simp only [atomicExponentialWeightMul_zero, ContinuousLinearMap.id_apply,
      hz', norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero] at h
    dsimp only [A, E₀]
    nlinarith only [h]
  let B := orthogonalCompression A (v : L2Space)
  have hB : IsSelfAdjoint B :=
    isSelfAdjoint_orthogonalCompression A (hApot coupling).selfAdjoint v hvnorm
  have hBlower : ∀ z : B.domain, (E₀ + hRad.gap / 2 * coupling) *
      ‖(z : orthogonalComplement (v : L2Space))‖ ^ 2 ≤
        (inner ℂ (z : orthogonalComplement (v : L2Space)) (B z)).re := by
    intro z
    rw [orthogonalCompression_inner]
    exact hbase (compressionDomainInclusion A (v : L2Space) z)
      (orthogonalComplement_inner_right (v : L2Space) (z : orthogonalComplement (v : L2Space)))
  have hdiag : schurDiagonal A v ≤ E₀ := by
    rw [schurDiagonal_eq_reference_add_residual A v hvnorm E₀ r hr]
    have hsign := re_inner_atomicPerturbationMul_nonpos hp (v : L2Space)
    have hrinner : (inner ℂ (v : L2Space) r).re =
        coupling ^ 2 * (inner ℂ (v : L2Space)
          (atomicPerturbationMul hp (v : L2Space))).re := by
      simp only [r, inner_smul_right, ← Complex.ofReal_pow, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hrinner]
    exact add_le_of_nonpos_right
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg coupling) hsign)
  let s : AtomicSchurReference p hp coupling (hRad.gap / 2 * coupling) := {
    coreState := φ
    coreGround := hφ
    vector := v
    represents := hvrep
    diagonal_le := hdiag
    coupling_le := schurCoupling_norm_le_residual A v hvnorm E₀ r hr
    diagonal_error_le := schurDiagonal_sub_reference_le_residual A v hvnorm E₀ r hr
    complement_lower := hbase
  }
  refine ⟨s, hpos, ?_⟩
  intro E hE
  obtain ⟨R, hR, _⟩ := exists_coerciveSelfAdjoint_resolvent B hB
    (mul_pos (half_pos hRad.gap_pos) hcoupling_pos) hBlower E hE
  refine ⟨R, hR, ?_⟩
  intro κ hκ
  have hκg' : κ ∈ Icc 0 κg := ⟨hκ.1, hκ.2.trans (min_le_left _ _)⟩
  have hκt' : κ ∈ Icc 0 κt := ⟨hκ.1, hκ.2.trans (min_le_right _ _)⟩
  let W := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
  let Wm := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling (-κ)
  have hW := isSelfAdjoint_atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
  have hWnorm : ∀ z : L2Space, ‖z‖ ≤ ‖W z‖ :=
    norm_le_atomicExponentialWeightMul χ.weight χ.weight_continuous hT
      hcoupling_pos.le hκ.1
  have ht := htail coupling hct κ hκt' φ hφ (v : L2Space) hvrep
  have hdifference : ‖W (v : L2Space) - (v : L2Space)‖ ≤
      C * Real.exp (-c * coupling) := by
    rw [← atomicExponentialWeightDefectMul_apply_eq_sub]
    exact ht.1
  have hrnorm := hresidual coupling hcr φ hφ (v : L2Space) hvrep
  have habsorb := (habsorption coupling hca).2
    ‖W (v : L2Space) - (v : L2Space)‖ ‖r‖ ‖W (v : L2Space)‖
    (norm_nonneg _) (norm_nonneg _) hdifference hrnorm ht.2
  have hweighted' : ∀ z : A.domain,
      (hRad.gap / 2 * coupling) * ‖W (z : L2Space)‖ ^ 2 -
        2 * (hRad.gap * coupling) * ‖inner ℂ (v : L2Space) (W (z : L2Space))‖ ^ 2 ≤
      (inner ℂ (W (z : L2Space)) (W (A z))).re - E₀ * ‖W (z : L2Space)‖ ^ 2 := by
    intro z
    simpa only [hv] using hweighted κ hκg' z
  have hRweighted (f : orthogonalComplement (v : L2Space)) :
      (hRad.gap / 4 * coupling) * ‖W (R f : L2Space)‖ ≤ ‖W (f : L2Space)‖ := by
    have h := weighted_compression_resolvent_bound A (hApot coupling).selfAdjoint v hvnorm
      E₀ r hr W hW hWnorm
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg hRad.gap_pos.le hcoupling_pos.le))
      (mul_pos (div_pos hRad.gap_pos (by norm_num)) hcoupling_pos) hE hweighted' habsorb R hR f
    have hmul := (le_div_iff₀ (mul_pos (div_pos hRad.gap_pos (by norm_num)) hcoupling_pos)).mp h
    simpa only [mul_comm] using hmul
  have hbound := norm_weightedProjectedResolvent_le (v : L2Space) hvnorm W Wm
    (atomicExponentialWeightMul_neg_cancel χ.weight χ.weight_continuous hT coupling κ)
    (norm_atomicExponentialWeightMul_neg_le χ.weight χ.weight_continuous hT
      hcoupling_pos.le hκ.1) R
    (mul_pos (div_pos hRad.gap_pos (by norm_num)) hcoupling_pos) hRweighted
  have hWφ : ‖W (v : L2Space)‖ ≤ 2 := by
    linarith only [ht.2, (habsorption coupling hca).1]
  have hden : 0 < hRad.gap / 4 * coupling :=
    mul_pos (div_pos hRad.gap_pos (by norm_num)) hcoupling_pos
  calc
    _ ≤ (1 + ‖W (v : L2Space)‖) / (hRad.gap / 4 * coupling) := hbound
    _ ≤ 3 / (hRad.gap / 4 * coupling) :=
      div_le_div_of_nonneg_right (by linarith only [hWφ]) hden.le
    _ = _ := by field_simp; ring

/-- The original weighted inverse interface follows from the stronger
construction retaining the same quantitative Schur reference. -/
theorem exists_atomic_cusp_weighted_inverse_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ threshold > 0, ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ ∧
      ∃ v : (magneticOperator p.b coupling p.potential).domain,
        Represents (v : L2Space) φ ∧ ‖(v : L2Space)‖ = 1 ∧
        ∀ E : ℝ, E ≤ atomicGroundEnergy p.b p.core coupling →
        ∃ R : orthogonalComplement (v : L2Space) →L[ℂ] orthogonalComplement (v : L2Space),
          IsOperatorResolvent (orthogonalCompression
            (magneticOperator p.b coupling p.potential) (v : L2Space)) E R ∧
          ∀ κ ∈ Icc 0 κ₀,
            ‖weightedProjectedResolvent (v : L2Space)
              (atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ)
              (atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling (-κ)) R‖ ≤
                12 / (hRad.gap * coupling) := by
  obtain ⟨M, hM, hT, κ₀, hκ₀, threshold, hthreshold, hreference⟩ :=
    exists_atomic_cusp_weighted_reference_of_radialData hp hRad hAcore hApot χ
  refine ⟨M, hM, hT, κ₀, hκ₀, threshold, hthreshold, ?_⟩
  intro coupling hc
  obtain ⟨s, _, hR⟩ := hreference coupling hc
  exact ⟨s.coreState, s.coreGround, s.vector, s.represents, s.vector_norm, hR⟩

end InfiniteZero.CuspParameters
