import InfiniteZero.ParityTrialEnergyBound
import InfiniteZero.PhysicalEigenmodeTransfer

/-!
# Squared physical residuals control both normalized parity trials

When the overlap has magnitude at most one half, the normalization factor
has norm at most one. The squared trial residual is therefore at most
twice the sum of the squared left and right residuals. This is the scale
needed in the quadratic Schur bound, before any asymptotic comparison.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem norm_signed_trial_residual_sq_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (E : ℝ) (uLeft uRight : A.domain)
    (even : Bool) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖A (c • (if even then uLeft + uRight else uLeft - uRight)) -
      (E : ℂ) • ((c • (if even then uLeft + uRight else uLeft - uRight) : A.domain) : H)‖ ^ 2 ≤
      2 * (‖A uLeft - (E : ℂ) • (uLeft : H)‖ ^ 2 +
        ‖A uRight - (E : ℂ) • (uRight : H)‖ ^ 2) := by
  let rL := A uLeft - (E : ℂ) • (uLeft : H)
  let rR := A uRight - (E : ℂ) • (uRight : H)
  have heq : A (c • (if even then uLeft + uRight else uLeft - uRight)) -
      (E : ℂ) • ((c • (if even then uLeft + uRight else uLeft - uRight) : A.domain) : H) =
      c • (if even then rL + rR else rL - rR) := by
    cases even <;>
      simp only [Bool.false_eq_true, ↓reduceIte, LinearPMap.map_smul,
        LinearPMap.map_add, LinearPMap.map_sub, Submodule.coe_smul,
        Submodule.coe_add, Submodule.coe_sub, rL, rR] <;> module
  have hn : ‖c • (if even then rL + rR else rL - rR)‖ ≤ ‖rL‖ + ‖rR‖ := by
    rw [norm_smul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
    cases even
    · exact norm_sub_le rL rR
    · exact norm_add_le rL rR
  rw [heq]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  change _ ≤ 2 * (‖rL‖ ^ 2 + ‖rR‖ ^ 2)
  nlinarith only [hsq, sq_nonneg (‖rL‖ - ‖rR‖)]

theorem norm_normalizedParityTrial_residual_sq_le
    {b L coupling : ℝ} {φ : Wavefunction}
    (A : L2Space →ₗ.[ℂ] L2Space) (E : ℝ) (uLeft uRight q : A.domain)
    (hLeft : Represents (uLeft : L2Space) (leftState b L coupling φ))
    (hRight : Represents (uRight : L2Space) (rightState b L coupling φ))
    (even : Bool)
    (hq : Represents (q : L2Space) (normalizedParityTrialState even b L coupling φ))
    (hs : |translatedOverlap b L coupling φ| ≤ 1 / 2) :
    ‖A q - (E : ℂ) • (q : L2Space)‖ ^ 2 ≤
      2 * (‖A uLeft - (E : ℂ) • (uLeft : L2Space)‖ ^ 2 +
        ‖A uRight - (E : ℂ) • (uRight : L2Space)‖ ^ 2) := by
  let raw : A.domain := if even then uLeft + uRight else uLeft - uRight
  have hraw : Represents (raw : L2Space) (parityTrialState even b L coupling φ) := by
    cases even
    · change Represents ((uLeft : L2Space) - (uRight : L2Space))
        (leftState b L coupling φ - rightState b L coupling φ)
      filter_upwards [Lp.coeFn_sub (uLeft : L2Space) (uRight : L2Space),
        hLeft, hRight] with x hx hxl hxr
      simpa only [Pi.sub_apply, hxl, hxr] using hx
    · exact hLeft.add hRight
  let c : ℂ := ((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ)
  have hr : Represents ((c • raw : A.domain) : L2Space)
      (normalizedParityTrialState even b L coupling φ) := hraw.smul c
  have hqeq : q = c • raw := Subtype.ext (Lp.ext (hq.trans hr.symm))
  rw [hqeq]
  exact norm_signed_trial_residual_sq_le A E uLeft uRight even c
    (norm_parityTrial_normalization_le_one even hs)

end InfiniteZero
