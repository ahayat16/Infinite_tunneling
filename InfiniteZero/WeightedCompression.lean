import InfiniteZero.OrthogonalSchurGeometry
import InfiniteZero.CoerciveResolvent

/-!
# Lifting compressed equations and controlling weighted orthogonality

The component omitted by the actual orthogonal compression is expressed in
terms of a reference vector's residual. A bounded self-adjoint multiplier
has an equally explicit orthogonality defect. These are domain and Hilbert
space identities; no weighted inverse is assumed or constructed here.
-/

noncomputable section

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Symmetry moves the missing component to the given reference residual. -/
theorem compression_lift_coefficient_eq_of_residual
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (φ : A.domain)
    (E₀ : ℝ) (r : H) (hr : A φ = (E₀ : ℂ) • (φ : H) + r)
    (ζ : (orthogonalCompression A (φ : H)).domain) :
    inner ℂ (φ : H) (A (compressionDomainInclusion A (φ : H) ζ)) =
      inner ℂ r ((ζ : orthogonalComplement (φ : H)) : H) := by
  have hs := selfAdjoint_inner_of_mem_graph hA (A.mem_graph φ)
    (A.mem_graph (compressionDomainInclusion A (φ : H) ζ))
  calc
    _ = inner ℂ (A φ) ((ζ : orthogonalComplement (φ : H)) : H) := hs.symm
    _ = _ := by
      rw [hr, inner_add_left, inner_smul_left,
        orthogonalComplement_inner_right, mul_zero, zero_add]

/-- The compressed vector belongs to the genuine original domain. The
uncompressed equation differs by precisely one residual component. -/
theorem compression_lift_eq_of_residual
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (E₀ : ℝ) (r : H)
    (hr : A φ = (E₀ : ℂ) • (φ : H) + r)
    (ζ : (orthogonalCompression A (φ : H)).domain) :
    A (compressionDomainInclusion A (φ : H) ζ) =
      (orthogonalCompression A (φ : H) ζ : H) +
        inner ℂ r ((ζ : orthogonalComplement (φ : H)) : H) • (φ : H) := by
  rw [orthogonalCompression_apply, complementProjection_coe (φ : H) hφ,
    compression_lift_coefficient_eq_of_residual A hA φ E₀ r hr ζ]
  exact (sub_add_cancel _ _).symm

/-- The same exact lifting identity after any real energy shift. Both
shifted operators keep their original concrete domains. -/
theorem compression_lift_shifted_eq_of_residual
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (E₀ : ℝ) (r : H)
    (hr : A φ = (E₀ : ℂ) • (φ : H) + r) (E : ℝ)
    (ζ : (orthogonalCompression A (φ : H)).domain) :
    shiftedOperator A E (compressionDomainInclusion A (φ : H) ζ) =
      (shiftedOperator (orthogonalCompression A (φ : H)) E ζ : H) +
        inner ℂ r ((ζ : orthogonalComplement (φ : H)) : H) • (φ : H) := by
  simp only [shiftedOperator_apply, Submodule.coe_sub, Submodule.coe_smul]
  rw [compression_lift_eq_of_residual A hA φ hφ E₀ r hr ζ]
  change (orthogonalCompression A (φ : H) ζ : H) +
      inner ℂ r ((ζ : orthogonalComplement (φ : H)) : H) • (φ : H) -
      (E : ℂ) • ((ζ : orthogonalComplement (φ : H)) : H) = _
  module

theorem compression_lift_residual_coefficient_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (φ : A.domain)
    (E₀ : ℝ) (r : H) (hr : A φ = (E₀ : ℂ) • (φ : H) + r)
    (ζ : (orthogonalCompression A (φ : H)).domain) :
    ‖inner ℂ (φ : H) (A (compressionDomainInclusion A (φ : H) ζ))‖ ≤
      ‖r‖ * ‖(ζ : orthogonalComplement (φ : H))‖ := by
  rw [compression_lift_coefficient_eq_of_residual A hA φ E₀ r hr ζ]
  exact norm_inner_le_norm _ _

/-- For a self-adjoint multiplier the loss of orthogonality is exactly its
error on the reference vector. No norm-one assumption is needed here. -/
theorem weighted_orthogonality_identity (M : H →L[ℂ] H) (hM : IsSelfAdjoint M)
    (φ u : H) (hu : inner ℂ φ u = 0) :
    inner ℂ φ (M u) = inner ℂ (M φ - φ) u := by
  rw [inner_sub_left, hu, sub_zero]
  exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hM) φ u).symm

theorem weighted_orthogonality_defect_le (M : H →L[ℂ] H) (hM : IsSelfAdjoint M)
    (φ u : H) (hu : inner ℂ φ u = 0) :
    ‖inner ℂ φ (M u)‖ ≤ ‖M φ - φ‖ * ‖u‖ := by
  rw [weighted_orthogonality_identity M hM φ u hu]
  exact norm_inner_le_norm _ _

/-- For a norm-expanding weight the original-vector factor may be replaced
by its weighted norm. -/
theorem weighted_orthogonality_defect_le_weighted_norm
    (M : H →L[ℂ] H) (hM : IsSelfAdjoint M)
    (hMnorm : ∀ v : H, ‖v‖ ≤ ‖M v‖)
    (φ u : H) (hu : inner ℂ φ u = 0) :
    ‖inner ℂ φ (M u)‖ ≤ ‖M φ - φ‖ * ‖M u‖ :=
  (weighted_orthogonality_defect_le M hM φ u hu).trans
    (mul_le_mul_of_nonneg_left (hMnorm u) (norm_nonneg _))

end InfiniteZero
