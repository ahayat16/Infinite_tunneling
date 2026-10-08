import InfiniteZero.CanonicalParityCorrectionMass
import InfiniteZero.OppositeSupportEnvelopeComparison

/-!
# From the opposite-support integrals to the common fine envelope

The diagonal defect costs two powers of the coupling. The proved quadratic
Schur correction costs three. Both are compared to the same fifteenth-power
majorant, retaining the actual core and full-state actions and coefficients.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem canonicalDefect_le_oppositeSupportFineBound
    {p : CuspParameters} {L coupling c Γ C : ℝ}
    (hc : 1 ≤ coupling) (hC : 0 ≤ C)
    (hI : |∫ x : Plane, p.potential (x + displacement L) *
        ‖rightState p.b L coupling (canonicalAtomicState p.b p.potential coupling) x‖ ^ 2| ≤
      C * c ^ 2 * Γ ^ 2 * coupling ^ 12 *
        Real.exp (-2 * coupling *
          (bridgeAction p.b (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
            bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)))) :
    |canonicalDefect p.b p.potential L coupling| ≤
      p.oppositeSupportFineBound L C coupling c Γ := by
  have hc0 : 0 ≤ coupling := zero_le_one.trans hc
  rw [canonicalDefect_eq_right, abs_mul, abs_of_nonneg (sq_nonneg coupling)]
  let D := bridgeAction p.b
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
    bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)
  change coupling ^ 2 * _ ≤ C * c ^ 2 * Γ ^ 2 * coupling ^ 15 * Real.exp (-2 * coupling * D)
  calc
    _ ≤ coupling ^ 2 *
        (C * c ^ 2 * Γ ^ 2 * coupling ^ 12 * Real.exp (-2 * coupling * D)) :=
      mul_le_mul_of_nonneg_left hI (sq_nonneg coupling)
    _ = C * c ^ 2 * Γ ^ 2 * coupling ^ 14 * Real.exp (-2 * coupling * D) := by ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hc (by norm_num : (14 : ℕ) ≤ 15)) (by positivity))
        (Real.exp_pos _).le

theorem canonicalParityCorrection_le_oppositeSupportFineBound
    {p : CuspParameters} {L coupling c Γ C g : ℝ}
    (hc : 0 ≤ coupling) (hg : 0 < g) (even : Bool)
    (hσ : canonicalParityCorrection p.b p.potential L coupling even ≤
      (32 / g) * coupling ^ 3 * canonicalOppositeMass p.b p.potential L coupling)
    (hM : canonicalOppositeMass p.b p.potential L coupling ≤
      C * c ^ 2 * Γ ^ 2 * coupling ^ 12 *
        Real.exp (-2 * coupling *
          (bridgeAction p.b (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
            bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)))) :
    canonicalParityCorrection p.b p.potential L coupling even ≤
      p.oppositeSupportFineBound L ((32 / g) * C) coupling c Γ := by
  apply hσ.trans
  calc
    _ ≤ (32 / g) * coupling ^ 3 *
        (C * c ^ 2 * Γ ^ 2 * coupling ^ 12 *
          Real.exp (-2 * coupling *
            (bridgeAction p.b (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
              bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)))) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = _ := by unfold oppositeSupportFineBound; ring

end InfiniteZero.CuspParameters
