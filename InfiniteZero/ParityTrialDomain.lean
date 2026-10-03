import InfiniteZero.DoubleWellTrialDomain
import InfiniteZero.ParityTrialStates

/-!
# Normalized parity trials in the genuine double-well domain

The translated atomic vectors lie in the double-well operator domain by
bounded perturbation. This domain is a complex vector space, so their
normalized sum and difference also belong to it. Their representatives
have the exact parity and, when the overlap is smaller than one, unit norm.
These trial vectors are not asserted to be eigenvectors.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

theorem IsAtomicGroundState.exists_normalizedParityTrialState_operator_vector
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) :
    ∃ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      Represents (u : L2Space) (normalizedParityTrialState even b L coupling φ) ∧
      HasL2Parity even (u : L2Space) := by
  obtain ⟨uLeft, hLeft, _, _⟩ :=
    hφ.exists_leftState_double_operator_vector hv hbound hAleft hAdouble
  obtain ⟨uRight, hRight, _, _⟩ :=
    hφ.exists_rightState_double_operator_vector hv hbound hAright hAdouble
  let uRaw : (magneticOperator b coupling (doubleWellPotential v L)).domain :=
    if even then uLeft + uRight else uLeft - uRight
  have hRaw : Represents (uRaw : L2Space) (parityTrialState even b L coupling φ) := by
    cases even
    · change Represents ((uLeft : L2Space) - (uRight : L2Space))
        (leftState b L coupling φ - rightState b L coupling φ)
      filter_upwards [Lp.coeFn_sub (uLeft : L2Space) (uRight : L2Space),
        hLeft, hRight] with x hx hxl hxr
      simpa only [Pi.sub_apply, hxl, hxr] using hx
    · change Represents ((uLeft : L2Space) + (uRight : L2Space))
        (leftState b L coupling φ + rightState b L coupling φ)
      filter_upwards [Lp.coeFn_add (uLeft : L2Space) (uRight : L2Space),
        hLeft, hRight] with x hx hxl hxr
      simpa only [Pi.add_apply, hxl, hxr] using hx
  let c : ℂ := ((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ)
  let u : (magneticOperator b coupling (doubleWellPotential v L)).domain := c • uRaw
  have hu : Represents (u : L2Space) (normalizedParityTrialState even b L coupling φ) := by
    change Represents (c • (uRaw : L2Space)) (c • parityTrialState even b L coupling φ)
    filter_upwards [Lp.coeFn_smul c (uRaw : L2Space), hRaw] with x hx hraw
    simpa only [Pi.smul_apply, hraw] using hx
  exact ⟨u, hu, hu.hasL2Parity (normalizedParityTrialState_hasParity even b L coupling φ)⟩

theorem IsAtomicGroundState.exists_normalizedParityTrialState_unit_operator_vector
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) (hs : |translatedOverlap b L coupling φ| < 1) :
    ∃ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      Represents (u : L2Space) (normalizedParityTrialState even b L coupling φ) ∧
      ‖(u : L2Space)‖ = 1 ∧ HasL2Parity even (u : L2Space) := by
  obtain ⟨u, hu, hp⟩ := hφ.exists_normalizedParityTrialState_operator_vector
    hv hbound hAleft hAright hAdouble even
  refine ⟨u, hu, ?_, hp⟩
  have hnorm := hu.norm_sq_eq_mass.trans
    (mass_normalizedParityTrialState even b L coupling hφ.1.2.1 hφ.2 hs)
  nlinarith [norm_nonneg (u : L2Space)]

end InfiniteZero
