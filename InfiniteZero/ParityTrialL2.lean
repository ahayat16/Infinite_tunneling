import InfiniteZero.ParityTrialComplement
import InfiniteZero.ParityTrialStates
import InfiniteZero.AtomicGroundTransfer

/-!
# Physical normalized parity trials and their L² complement

The same signed sum defines the physical trial and its Hilbert-space
representative. Therefore, inside either parity sector, orthogonality to
that normalized trial removes both atomic overlaps from the proved
physical two-well coercivity estimate.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem Represents.normalizedParityTrialState
    {b L coupling : ℝ} {φ : Wavefunction} {v : L2Space}
    (hv : Represents v (leftState b L coupling φ)) (even : Bool) :
    Represents
      (((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ) •
        (if even then v + l2Inversion v else v - l2Inversion v))
      (normalizedParityTrialState even b L coupling φ) := by
  have hr : Represents (l2Inversion v) (rightState b L coupling φ) := hv.inversion
  have hraw : Represents (if even then v + l2Inversion v else v - l2Inversion v)
      (parityTrialState even b L coupling φ) := by
    cases even
    · change Represents (v - l2Inversion v)
        (leftState b L coupling φ - rightState b L coupling φ)
      filter_upwards [Lp.coeFn_sub v (l2Inversion v), hv, hr] with x hx hl hh
      simpa only [Pi.sub_apply, hl, hh] using hx
    · change Represents (v + l2Inversion v)
        (leftState b L coupling φ + rightState b L coupling φ)
      filter_upwards [Lp.coeFn_add v (l2Inversion v), hv, hr] with x hx hl hh
      simpa only [Pi.add_apply, hl, hh] using hx
  exact hraw.smul _

theorem normalizedParityTrial_complement_orthogonal
    (even : Bool) {b L coupling : ℝ} {φ : Wavefunction} {vL vR q u : L2Space}
    (hvL : Represents vL (leftState b L coupling φ))
    (hvR : Represents vR (rightState b L coupling φ))
    (hq : Represents q (normalizedParityTrialState even b L coupling φ))
    (hs : |translatedOverlap b L coupling φ| < 1)
    (hu : HasL2Parity even u) (horth : inner ℂ q u = 0) :
    inner ℂ vL u = 0 ∧ inner ℂ vR u = 0 := by
  let z : ℂ := ((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ)
  have hz : z ≠ 0 := by
    have hpos := Real.sqrt_pos.mpr (parityTrialMass_pos even hs)
    dsimp only [z]
    exact_mod_cast (inv_ne_zero hpos.ne')
  have hqeq : q = z • (if even then vL + l2Inversion vL else vL - l2Inversion vL) :=
    Lp.ext (hq.trans (hvL.normalizedParityTrialState even).symm)
  have hr : Represents (l2Inversion vL) (rightState b L coupling φ) := hvL.inversion
  have hvReq : vR = l2Inversion vL := Lp.ext (hvR.trans hr.symm)
  rw [hqeq] at horth
  rw [hvReq]
  exact parity_trial_complement_orthogonal even vL u hu hz horth

end InfiniteZero
