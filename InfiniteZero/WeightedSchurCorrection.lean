import InfiniteZero.SchurGroundQuantitative
import InfiniteZero.SchurResidualBounds
import InfiniteZero.WeightedProjectedResolvent

/-!
# The actual Schur correction through a weighted projected resolvent

The correction retained by a quantitative certificate is the resolvent of
the projected reference residual. Conjugation by mutually cancelling bounded
weights gives its weighted estimate, without commuting the projection with
the weight. Positive normalization can only reduce this correction.
-/

noncomputable section
set_option maxHeartbeats 800000
namespace InfiniteZero

namespace QuantitativeSchurGroundCertificate

variable {A : L2Space →ₗ.[ℂ] L2Space} {φ : A.domain} {E g : ℝ}
    (q : QuantitativeSchurGroundCertificate A φ E g)

theorem correction_eq_resolvent_residual (hA : IsSelfAdjoint A)
    (hφ : ‖(φ : L2Space)‖ = 1)
    (R : orthogonalComplement (φ : L2Space) →L[ℂ] orthogonalComplement (φ : L2Space))
    (hR : IsOperatorResolvent (orthogonalCompression A (φ : L2Space)) E R)
    (E₀ : ℝ) (r : L2Space) (hr : A φ = (E₀ : ℂ) • (φ : L2Space) + r) :
    (q.correction : orthogonalComplement (φ : L2Space)) =
      R (complementProjection (φ : L2Space) r) := by
  have hi := hR.left_inverse (isSelfAdjoint_orthogonalCompression A hA φ hφ)
    ((orthogonalCompression A (φ : L2Space)).mem_graph q.correction)
  dsimp only at hi
  simpa only [q.correction_equation, add_sub_cancel_right,
    schurCoupling_eq_projected_residual A φ hφ E₀ r hr] using hi.symm

/-- The projection remains inside the true conjugated resolvent. Only the
identity `N (M u) = u` is used; no self-adjointness of the weights is needed. -/
theorem weighted_correction_eq (hA : IsSelfAdjoint A) (hφ : ‖(φ : L2Space)‖ = 1)
    (R : orthogonalComplement (φ : L2Space) →L[ℂ] orthogonalComplement (φ : L2Space))
    (hR : IsOperatorResolvent (orthogonalCompression A (φ : L2Space)) E R)
    (E₀ : ℝ) (r : L2Space) (hr : A φ = (E₀ : ℂ) • (φ : L2Space) + r)
    (M N : L2Space →L[ℂ] L2Space) (hNM : ∀ u, N (M u) = u) :
    M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space) =
      weightedProjectedResolvent (φ : L2Space) M N R (M r) := by
  rw [q.correction_eq_resolvent_residual hA hφ R hR E₀ r hr]
  simp only [weightedProjectedResolvent, ContinuousLinearMap.comp_apply, hNM,
    Submodule.subtypeL_apply]

theorem norm_weighted_correction_le (hA : IsSelfAdjoint A) (hφ : ‖(φ : L2Space)‖ = 1)
    (R : orthogonalComplement (φ : L2Space) →L[ℂ] orthogonalComplement (φ : L2Space))
    (hR : IsOperatorResolvent (orthogonalCompression A (φ : L2Space)) E R)
    (E₀ : ℝ) (r : L2Space) (hr : A φ = (E₀ : ℂ) • (φ : L2Space) + r)
    (M N : L2Space →L[ℂ] L2Space) (hNM : ∀ u, N (M u) = u) :
    ‖M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space)‖ ≤
      ‖weightedProjectedResolvent (φ : L2Space) M N R‖ * ‖M r‖ := by
  rw [q.weighted_correction_eq hA hφ R hR E₀ r hr M N hNM]
  exact (weightedProjectedResolvent (φ : L2Space) M N R).le_opNorm _

theorem weighted_normalizedVector_sub_smul_eq (hφ : ‖(φ : L2Space)‖ = 1)
    (M : L2Space →L[ℂ] L2Space) :
    M ((q.certificate.normalizedVector : L2Space) -
      (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        (φ : L2Space)) =
      -(schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space) := by
  simp only [q.normalizedVector_coe_eq hφ, map_sub, map_smul]
  module

theorem norm_weighted_normalizedVector_sub_smul_le_correction
    (hφ : ‖(φ : L2Space)‖ = 1) (M : L2Space →L[ℂ] L2Space) :
    ‖M ((q.certificate.normalizedVector : L2Space) -
      (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        (φ : L2Space))‖ ≤
      ‖M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space)‖ := by
  simp only [q.weighted_normalizedVector_sub_smul_eq hφ M, norm_smul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (schurNormalization_pos (q.correction : orthogonalComplement (φ : L2Space)))]
  exact mul_le_of_le_one_left (norm_nonneg _) (schurNormalization_le_one _)

theorem norm_weighted_normalizedVector_sub_smul_eq
    (hφ : ‖(φ : L2Space)‖ = 1) (M : L2Space →L[ℂ] L2Space) :
    ‖M ((q.certificate.normalizedVector : L2Space) -
      (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        (φ : L2Space))‖ =
      schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) *
        ‖M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space)‖ := by
  simp only [q.weighted_normalizedVector_sub_smul_eq hφ M, norm_smul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (schurNormalization_pos (q.correction : orthogonalComplement (φ : L2Space)))]

theorem norm_weighted_normalizedVector_sub_smul_le
    (hA : IsSelfAdjoint A) (hφ : ‖(φ : L2Space)‖ = 1)
    (R : orthogonalComplement (φ : L2Space) →L[ℂ] orthogonalComplement (φ : L2Space))
    (hR : IsOperatorResolvent (orthogonalCompression A (φ : L2Space)) E R)
    (E₀ : ℝ) (r : L2Space) (hr : A φ = (E₀ : ℂ) • (φ : L2Space) + r)
    (M N : L2Space →L[ℂ] L2Space) (hNM : ∀ u, N (M u) = u) :
    ‖M ((q.certificate.normalizedVector : L2Space) -
      (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        (φ : L2Space))‖ ≤
      schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) *
        ‖weightedProjectedResolvent (φ : L2Space) M N R‖ * ‖M r‖ := by
  rw [q.norm_weighted_normalizedVector_sub_smul_eq hφ M, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (q.norm_weighted_correction_le hA hφ R hR E₀ r hr M N hNM)
    (schurNormalization_pos _).le

/-- Comparing directly to the unit reference retains the scalar
normalization loss as a separate term. -/
theorem norm_weighted_normalizedVector_sub_le (hφ : ‖(φ : L2Space)‖ = 1)
    (M : L2Space →L[ℂ] L2Space) :
    ‖M ((q.certificate.normalizedVector : L2Space) - (φ : L2Space))‖ ≤
      (1 - schurNormalization (q.correction : orthogonalComplement (φ : L2Space))) *
        ‖M (φ : L2Space)‖ +
      ‖M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space)‖ := by
  let c := schurNormalization (q.correction : orthogonalComplement (φ : L2Space))
  have hc : 0 < c := schurNormalization_pos _
  have hc1 : c ≤ 1 := schurNormalization_le_one _
  have heq : M ((q.certificate.normalizedVector : L2Space) - (φ : L2Space)) =
      ((c - 1 : ℝ) : ℂ) • M (φ : L2Space) -
        (c : ℂ) • M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space) := by
    simp only [q.normalizedVector_coe_eq hφ, map_sub, map_smul,
      Complex.ofReal_sub, Complex.ofReal_one, c]
    module
  calc
    _ ≤ ‖((c - 1 : ℝ) : ℂ) • M (φ : L2Space)‖ +
        ‖(c : ℂ) • M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space)‖ := by
      rw [heq]
      exact norm_sub_le _ _
    _ = (1 - c) * ‖M (φ : L2Space)‖ +
        c * ‖M ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space)‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr hc1), abs_of_pos hc, neg_sub]
    _ ≤ _ := add_le_add le_rfl
      (mul_le_of_le_one_left (norm_nonneg _) hc1)

end QuantitativeSchurGroundCertificate
end InfiniteZero
