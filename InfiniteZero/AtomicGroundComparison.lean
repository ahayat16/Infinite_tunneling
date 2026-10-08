import InfiniteZero.AtomicSchurReference
import InfiniteZero.SchurGroundQuantitative
import InfiniteZero.AtomicResidualDecay
import InfiniteZero.SchurExponentialBounds
import InfiniteZero.SchurNormalizedComparison

/-!
# Exponential energy comparison with the actual radial ground state

The residual in the core-to-full graph identity is exponentially small by
Agmon. A quantitative Schur certificate keeps the correction and the actual
ground energy tied to the same constructed eigenvector. No comparison of
energies or eigenfunctions is assumed.
-/

noncomputable section
namespace InfiniteZero

/-- The true ground energy is controlled by the actual reference residual.
The same certificate retains the small orthogonal correction. -/
theorem AtomicSchurReference.exists_ground_comparison {p : CuspParameters}
    {hp : p.BasicConditions} {coupling gap : ℝ}
    (h : AtomicSchurReference p hp coupling gap) (hg : 0 < gap)
    (hA : IsMagneticRealization p.b coupling p.potential) :
    ∃ q : QuantitativeSchurGroundCertificate
        (magneticOperator p.b coupling p.potential) h.vector
        (atomicGroundEnergy p.b p.potential coupling) gap,
      ‖(q.correction : orthogonalComplement (h.vector : L2Space))‖ ≤
        ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp
          (h.vector : L2Space)‖ / gap ∧
      0 ≤ atomicGroundEnergy p.b p.core coupling - atomicGroundEnergy p.b p.potential coupling ∧
      atomicGroundEnergy p.b p.core coupling - atomicGroundEnergy p.b p.potential coupling ≤
        ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp
          (h.vector : L2Space)‖ +
        ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp
          (h.vector : L2Space)‖ ^ 2 / gap := by
  obtain ⟨E, hE, ⟨q⟩⟩ := exists_quantitativeSchurGroundCertificate_of_complement_coercive
    (magneticOperator p.b coupling p.potential) hA.selfAdjoint
    h.vector h.vector_norm hg h.diagonal_le h.complement_lower
  have heq := hA.atomicGroundEnergy_eq_of_certificate q.certificate
  rw [heq]
  refine ⟨q, q.correction_norm_le.trans
    (div_le_div_of_nonneg_right h.coupling_le hg.le), sub_nonneg.mpr hE, ?_⟩
  have hdiagonal : atomicGroundEnergy p.b p.core coupling -
      schurDiagonal (magneticOperator p.b coupling p.potential) h.vector ≤
      ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp
        (h.vector : L2Space)‖ := by
    have hb := (abs_le.mp h.diagonal_error_le).1
    linarith only [hb]
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h.coupling_le
  have hsq := div_le_div_of_nonneg_right hs hg.le
  linarith only [hdiagonal, hsq, q.energy_shift_bounds.2]

namespace CuspParameters

/-- The full atomic energy differs exponentially little from the radial-core
energy. Constants and threshold are fixed before the coupling. -/
theorem exists_atomicGroundEnergy_exponential_comparison_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      0 ≤ atomicGroundEnergy p.b p.core coupling - atomicGroundEnergy p.b p.potential coupling ∧
      atomicGroundEnergy p.b p.core coupling - atomicGroundEnergy p.b p.potential coupling ≤
        C * Real.exp (-d * coupling) := by
  obtain ⟨K, hK, d, hd, Tr, hTr, hres⟩ :=
    exists_atomicResidual_decay_of_radialData hp hRad hAcore hApot
  obtain ⟨Ts, _, href⟩ := exists_atomicSchurReference_of_radialData hp hRad hAcore hApot
  let g := hRad.gap / 2
  have hg : 0 < g := half_pos hRad.gap_pos
  let M := K + K ^ 2 / g
  have hM : 0 < M := add_pos_of_pos_of_nonneg hK (div_nonneg (sq_nonneg K) hg.le)
  refine ⟨M * (2 / d), mul_pos hM (div_pos (by norm_num) hd), d / 2, half_pos hd,
    max Tr Ts, hTr.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcr : Tr ≤ coupling := (le_max_left _ _).trans hc
  have hcs : Ts ≤ coupling := (le_max_right _ _).trans hc
  have hcpos : 0 < coupling := hTr.trans_le hcr
  let s := Classical.choice (href coupling hcs)
  obtain ⟨q, _, hlo, hhi⟩ := s.exists_ground_comparison (mul_pos hg hcpos) (hApot coupling)
  have hr := hres coupling hcr s.coreState s.coreGround (s.vector : L2Space) s.represents
  have he := schur_residual_exponential_bound hK.le hd.le hg hcpos (norm_nonneg _) hr
  have habsorb := mul_le_mul_of_nonneg_left (linear_mul_exp_neg_le_half hd coupling) hM.le
  refine ⟨hlo, hhi.trans (he.trans ?_)⟩
  simpa only [M, mul_assoc] using habsorb

/-- Normalized genuine ground vectors of the two actual operators can be
chosen exponentially close. Their overlap is positive real, fixing the
relative phase; no assertion about the arbitrary canonical phase is needed. -/
theorem exists_atomicGroundVectors_exponential_comparison_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ u v : L2Space, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
        u ∈ operatorEigenspace (magneticOperator p.b coupling p.core)
          (atomicGroundEnergy p.b p.core coupling) ∧
        v ∈ operatorEigenspace (magneticOperator p.b coupling p.potential)
          (atomicGroundEnergy p.b p.potential coupling) ∧
        ‖v - u‖ ≤ C * Real.exp (-d * coupling) ∧
        0 < (inner ℂ u v).re ∧ (inner ℂ u v).im = 0 := by
  obtain ⟨K, hK, d, hd, Tr, hTr, hres⟩ :=
    exists_atomicResidual_decay_of_radialData hp hRad hAcore hApot
  obtain ⟨Ts, _, href⟩ := exists_atomicSchurReference_of_radialData hp hRad hAcore hApot
  let g := hRad.gap / 2
  have hg : 0 < g := half_pos hRad.gap_pos
  refine ⟨2 * K / g, div_pos (mul_pos (by norm_num) hK) hg, d, hd,
    max Tr Ts, hTr.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcr : Tr ≤ coupling := (le_max_left _ _).trans hc
  have hcs : Ts ≤ coupling := (le_max_right _ _).trans hc
  have hcpos : 0 < coupling := hTr.trans_le hcr
  let s := Classical.choice (href coupling hcs)
  obtain ⟨q, hcorr, _, _⟩ := s.exists_ground_comparison (mul_pos hg hcpos) (hApot coupling)
  have hr := hres coupling hcr s.coreState s.coreGround (s.vector : L2Space) s.represents
  have hcorrExp : ‖(q.correction : orthogonalComplement (s.vector : L2Space))‖ ≤
      K / g * Real.exp (-d * coupling) := by
    apply hcorr.trans
    calc
      _ ≤ (K * coupling * Real.exp (-d * coupling)) / (g * coupling) :=
        div_le_div_of_nonneg_right hr (mul_nonneg hg.le hcpos.le)
      _ = _ := by field_simp
  have hvEq : (q.certificate.normalizedVector : L2Space) =
      normalizedSchurVector (s.vector : L2Space)
        (q.correction : orthogonalComplement (s.vector : L2Space)) := by
    simpa only [normalizedSchurVector, schurNormalization] using
      q.normalizedVector_coe_eq s.vector_norm
  have hoverlap := inner_normalizedSchurVector (s.vector : L2Space) s.vector_norm
    (q.correction : orthogonalComplement (s.vector : L2Space))
  rw [← hvEq] at hoverlap
  refine ⟨s.vector, q.certificate.normalizedVector, s.vector_norm,
    q.certificate.normalizedVector_norm, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hAcore coupling).eigenfunction_iff _ (s.vector : L2Space)).mpr
      ⟨s.coreState, s.coreGround.1, s.represents⟩
  · rw [mem_operatorEigenspace]
    exact q.certificate.normalizedVector_eigenvector ▸
      (magneticOperator p.b coupling p.potential).mem_graph q.certificate.normalizedVector
  · rw [hvEq]
    calc
      _ ≤ 2 * ‖(q.correction : orthogonalComplement (s.vector : L2Space))‖ :=
        normalizedSchurVector_sub_norm_le _ s.vector_norm _
      _ ≤ 2 * (K / g * Real.exp (-d * coupling)) :=
        mul_le_mul_of_nonneg_left hcorrExp (by norm_num)
      _ = _ := by ring
  · rw [hoverlap, Complex.ofReal_re]
    exact schurNormalization_pos _
  · rw [hoverlap, Complex.ofReal_im]

end CuspParameters
end InfiniteZero
