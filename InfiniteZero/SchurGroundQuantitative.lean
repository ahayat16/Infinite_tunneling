import InfiniteZero.SchurGroundState
import InfiniteZero.SchurGroundEstimates
import InfiniteZero.GroundStateCertificate

/-!
# A quantitative certificate from one Schur root

The certificate, its domain correction and the quantitative bounds below all
come from the same scalar root. In particular, the certified vector retains
the reference coefficient one before normalization. No identification between
independent choices of eigenvectors is required.
-/

noncomputable section

namespace InfiniteZero

/-- The ground-state certificate together with its actual Schur correction.
Both equations and the exact reconstructed vector are retained for subsequent
estimates on normalized states. -/
structure QuantitativeSchurGroundCertificate
    (A : L2Space →ₗ.[ℂ] L2Space) (φ : A.domain) (E g : ℝ) where
  certificate : GroundStateCertificate A E
  correction : (orthogonalCompression A (φ : L2Space)).domain
  vector_eq : certificate.vector = φ - compressionDomainInclusion A (φ : L2Space) correction
  gap_eq : certificate.gap = g
  correction_equation : orthogonalCompression A (φ : L2Space) correction =
    schurCoupling A φ + (E : ℂ) • (correction : orthogonalComplement (φ : L2Space))
  scalar_equation : inner ℂ (φ : L2Space) (A φ) - (E : ℂ) -
    inner ℂ (schurCoupling A φ) (correction : orthogonalComplement (φ : L2Space)) = 0
  correction_norm_le : ‖(correction : orthogonalComplement (φ : L2Space))‖ ≤
    ‖schurCoupling A φ‖ / g
  energy_shift_bounds : 0 ≤ schurDiagonal A φ - E ∧
    schurDiagonal A φ - E ≤ ‖schurCoupling A φ‖ ^ 2 / g

/-- Construct one root, certify its reconstructed vector as the ground state,
and bound that same root's correction and energy shift. -/
theorem exists_quantitativeSchurGroundCertificate_of_complement_coercive
    (A : L2Space →ₗ.[ℂ] L2Space) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : L2Space)‖ = 1) {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal A φ ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : L2Space) (u : L2Space) = 0 →
      (E₀ + g) * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re) :
    ∃ E ≤ E₀, Nonempty (QuantitativeSchurGroundCertificate A φ E g) := by
  obtain ⟨E, hE, ζ, hζ, hs⟩ := exists_schur_root_data A hA φ hφ hg hdiag hbound
  let w : A.domain := φ - compressionDomainInclusion A (φ : L2Space) ζ
  have hw0 : (w : L2Space) ≠ 0 := schur_eigenvector_ne_zero (φ : L2Space) hφ _
  have hw : A w = (E : ℂ) • (w : L2Space) := by
    obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp (schur_eigenvector_graph A hA φ hφ E ζ hζ hs)
    have hvw : v = w := Subtype.ext hv
    simpa only [hvw] using hAv
  have hgap (u : A.domain) (hu : inner ℂ (w : L2Space) (u : L2Space) = 0) :
      g * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space) (A u)).re - E * ‖(u : L2Space)‖ ^ 2 :=
    schur_groundVector_gap A hA φ hφ ζ hg.le hE.2 hw hbound u hu
  let cert : GroundStateCertificate A E := {
    vector := w
    vector_ne_zero := hw0
    eigenvector := hw
    lower_bound := by
      intro u
      have h := shiftedEnergy_nonneg_of_complement A hA hg.le w hw0 hw hgap u
      linarith only [h]
    gap := g
    gap_pos := hg
    gap_bound := by
      intro u hu
      have h := hgap u hu
      nlinarith only [h]
  }
  exact ⟨E, hE.2, ⟨{
    certificate := cert
    correction := ζ
    vector_eq := rfl
    gap_eq := rfl
    correction_equation := hζ
    scalar_equation := hs
    correction_norm_le := schur_correction_norm_le A φ hg hE.2 hbound ζ hζ
    energy_shift_bounds := schur_energy_shift_bounds A φ hg hE.2 hbound ζ hζ hs
  }⟩⟩

namespace QuantitativeSchurGroundCertificate

variable {A : L2Space →ₗ.[ℂ] L2Space} {φ : A.domain} {E g : ℝ}
    (q : QuantitativeSchurGroundCertificate A φ E g)

/-- The retained vector identity is also an identity in the ambient Hilbert space. -/
theorem vector_coe_eq :
    (q.certificate.vector : L2Space) = (φ : L2Space) -
      ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space) := by
  rw [q.vector_eq]
  rfl

theorem vector_norm_sq (hφ : ‖(φ : L2Space)‖ = 1) :
    ‖(q.certificate.vector : L2Space)‖ ^ 2 =
      1 + ‖(q.correction : orthogonalComplement (φ : L2Space))‖ ^ 2 := by
  rw [q.vector_coe_eq]
  exact schur_groundVector_norm_sq (φ : L2Space) hφ _

theorem vector_norm (hφ : ‖(φ : L2Space)‖ = 1) :
    ‖(q.certificate.vector : L2Space)‖ =
      Real.sqrt (1 + ‖(q.correction : orthogonalComplement (φ : L2Space))‖ ^ 2) := by
  rw [← q.vector_norm_sq hφ, Real.sqrt_sq (norm_nonneg _)]

/-- Exact normalization in the original operator domain, using the positive
real coefficient already estimated in `SchurGroundEstimates`. -/
theorem normalizedVector_eq (hφ : ‖(φ : L2Space)‖ = 1) :
    q.certificate.normalizedVector =
      (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        (φ - compressionDomainInclusion A (φ : L2Space) q.correction) := by
  exact congrArg₂ (fun (c : ℂ) (v : A.domain) => c • v)
    (congrArg (fun r : ℝ => ((r⁻¹ : ℝ) : ℂ)) (q.vector_norm hφ)) q.vector_eq

theorem normalizedVector_coe_eq (hφ : ‖(φ : L2Space)‖ = 1) :
    (q.certificate.normalizedVector : L2Space) =
      (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        ((φ : L2Space) -
          ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space)) := by
  rw [q.normalizedVector_eq hφ]
  rfl

end QuantitativeSchurGroundCertificate
end InfiniteZero
