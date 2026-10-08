import InfiniteZero.MagneticCovariance
import InfiniteZero.WavefunctionL2Bridge

/-!
# The genuine even and odd two-well trial states

Inversion exchanges the magnetic left and right states. Their overlap is
therefore real. The symmetric and antisymmetric combinations have the
exact masses used in the parity reduction and can be normalized when
the absolute overlap is less than one. No eigenfunction assertion is made.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace InfiniteZero

theorem memLp_leftState (b L coupling : ℝ) {φ : Wavefunction}
    (hφ : MemLp φ 2 volume) : MemLp (leftState b L coupling φ) 2 volume := by
  let a := -displacement L
  have hshift := hφ.comp_measurePreserving (measurePreserving_sub_right volume a)
  have hphase : Continuous (fun x : Plane =>
      Complex.exp (-Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ))) := by
    unfold wedge
    fun_prop
  apply hshift.congr_norm
    (hphase.aestronglyMeasurable.mul hshift.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x =>
    (norm_magneticTranslation b coupling a φ x).symm

theorem memLp_rightState (b L coupling : ℝ) {φ : Wavefunction}
    (hφ : MemLp φ 2 volume) : MemLp (rightState b L coupling φ) 2 volume :=
  (memLp_leftState b L coupling hφ).comp_measurePreserving volume.measurePreserving_neg

theorem mass_leftState (b L coupling : ℝ) (φ : Wavefunction) :
    mass (leftState b L coupling φ) = mass φ :=
  mass_magneticTranslation b coupling (-displacement L) φ

theorem mass_rightState (b L coupling : ℝ) (φ : Wavefunction) :
    mass (rightState b L coupling φ) = mass φ := by
  change mass (fun x => leftState b L coupling φ (-x)) = mass φ
  rw [mass_inversion, mass_leftState]

theorem waveInner_inversion (φ ψ : Wavefunction) :
    waveInner (fun x => φ (-x)) (fun x => ψ (-x)) = waveInner φ ψ :=
  integral_neg_eq_self (fun x => star (φ x) * ψ x) volume

theorem waveInner_star_swap (φ ψ : Wavefunction) :
    star (waveInner φ ψ) = waveInner ψ φ := by
  simp only [waveInner, Complex.star_def, ← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

/-- Reality needs only inversion symmetry, even before an L² hypothesis. -/
theorem waveInner_left_right_im_eq_zero (b L coupling : ℝ) (φ : Wavefunction) :
    (waveInner (leftState b L coupling φ) (rightState b L coupling φ)).im = 0 := by
  have hinv := waveInner_inversion (leftState b L coupling φ) (rightState b L coupling φ)
  have hs : waveInner (rightState b L coupling φ) (leftState b L coupling φ) =
      waveInner (leftState b L coupling φ) (rightState b L coupling φ) := by
    simpa only [rightState, neg_neg] using hinv
  have hi := congrArg Complex.im ((waveInner_star_swap
    (leftState b L coupling φ) (rightState b L coupling φ)).trans hs)
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

def translatedOverlap (b L coupling : ℝ) (φ : Wavefunction) : ℝ :=
  (waveInner (leftState b L coupling φ) (rightState b L coupling φ)).re

theorem waveInner_left_right_eq_overlap (b L coupling : ℝ) (φ : Wavefunction) :
    waveInner (leftState b L coupling φ) (rightState b L coupling φ) =
      (translatedOverlap b L coupling φ : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using waveInner_left_right_im_eq_zero b L coupling φ

theorem mass_add_wavefunctions {φ ψ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) :
    mass (φ + ψ) = mass φ + 2 * (waveInner φ ψ).re + mass ψ := by
  rw [← norm_toLp_sq_eq_mass (hφ.add hψ), MemLp.toLp_add hφ hψ, norm_add_sq (𝕜 := ℂ),
    inner_toLp_eq_waveInner hφ hψ, norm_toLp_sq_eq_mass hφ, norm_toLp_sq_eq_mass hψ]
  rfl

theorem mass_sub_wavefunctions {φ ψ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) :
    mass (φ - ψ) = mass φ - 2 * (waveInner φ ψ).re + mass ψ := by
  rw [← norm_toLp_sq_eq_mass (hφ.sub hψ), MemLp.toLp_sub hφ hψ, norm_sub_sq (𝕜 := ℂ),
    inner_toLp_eq_waveInner hφ hψ, norm_toLp_sq_eq_mass hφ, norm_toLp_sq_eq_mass hψ]
  rfl

theorem mass_smul_wavefunction (z : ℂ) (φ : Wavefunction) :
    mass (z • φ) = ‖z‖ ^ 2 * mass φ := by
  simp only [mass, Pi.smul_apply, norm_smul, mul_pow, integral_const_mul]

def parityTrialState (even : Bool) (b L coupling : ℝ) (φ : Wavefunction) : Wavefunction :=
  if even then leftState b L coupling φ + rightState b L coupling φ
  else leftState b L coupling φ - rightState b L coupling φ

def parityTrialMass (even : Bool) (b L coupling : ℝ) (φ : Wavefunction) : ℝ :=
  if even then 2 * (1 + translatedOverlap b L coupling φ)
  else 2 * (1 - translatedOverlap b L coupling φ)

def normalizedParityTrialState (even : Bool) (b L coupling : ℝ)
    (φ : Wavefunction) : Wavefunction :=
  ((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ) •
    parityTrialState even b L coupling φ

theorem parityTrialState_hasParity (even : Bool) (b L coupling : ℝ) (φ : Wavefunction) :
    HasParity even (parityTrialState even b L coupling φ) := by
  cases even <;> intro x <;>
    simp [parityTrialState, rightState, sub_eq_add_neg, add_comm]

theorem memLp_parityTrialState (even : Bool) (b L coupling : ℝ) {φ : Wavefunction}
    (hφ : MemLp φ 2 volume) : MemLp (parityTrialState even b L coupling φ) 2 volume := by
  cases even
  · exact (memLp_leftState b L coupling hφ).sub (memLp_rightState b L coupling hφ)
  · exact (memLp_leftState b L coupling hφ).add (memLp_rightState b L coupling hφ)

theorem mass_parityTrialState (even : Bool) (b L coupling : ℝ) {φ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hm : mass φ = 1) :
    mass (parityTrialState even b L coupling φ) = parityTrialMass even b L coupling φ := by
  cases even <;> simp only [parityTrialState, parityTrialMass, Bool.false_eq_true,
    ↓reduceIte]
  · rw [mass_sub_wavefunctions (memLp_leftState b L coupling hφ)
      (memLp_rightState b L coupling hφ), mass_leftState, mass_rightState, hm]
    dsimp [translatedOverlap]
    ring
  · rw [mass_add_wavefunctions (memLp_leftState b L coupling hφ)
      (memLp_rightState b L coupling hφ), mass_leftState, mass_rightState, hm]
    dsimp [translatedOverlap]
    ring

theorem parityTrialMass_pos (even : Bool) {b L coupling : ℝ} {φ : Wavefunction}
    (hs : |translatedOverlap b L coupling φ| < 1) :
    0 < parityTrialMass even b L coupling φ := by
  have h := abs_lt.mp hs
  cases even <;> simp only [parityTrialMass, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem normalizedParityTrialState_hasParity
    (even : Bool) (b L coupling : ℝ) (φ : Wavefunction) :
    HasParity even (normalizedParityTrialState even b L coupling φ) := by
  have hp := parityTrialState_hasParity even b L coupling φ
  intro x
  simp only [normalizedParityTrialState, Pi.smul_apply, smul_eq_mul, hp x]
  cases even <;> simp

theorem memLp_normalizedParityTrialState
    (even : Bool) (b L coupling : ℝ) {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    MemLp (normalizedParityTrialState even b L coupling φ) 2 volume :=
  (memLp_parityTrialState even b L coupling hφ).const_smul _

theorem mass_normalizedParityTrialState
    (even : Bool) (b L coupling : ℝ) {φ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hm : mass φ = 1)
    (hs : |translatedOverlap b L coupling φ| < 1) :
    mass (normalizedParityTrialState even b L coupling φ) = 1 := by
  have hpos := parityTrialMass_pos even hs
  rw [normalizedParityTrialState, mass_smul_wavefunction,
    mass_parityTrialState even b L coupling hφ hm]
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

theorem waveInner_eq_zero_of_even_odd {φ ψ : Wavefunction}
    (hφ : HasParity true φ) (hψ : HasParity false ψ) : waveInner φ ψ = 0 := by
  have hi := waveInner_inversion φ ψ
  change (∀ x, φ (-x) = φ x) at hφ
  change (∀ x, ψ (-x) = -ψ x) at hψ
  simp only [waveInner, hφ, hψ, mul_neg, integral_neg] at hi
  have hre := congrArg Complex.re hi
  have him := congrArg Complex.im hi
  apply Complex.ext
  · change (∫ x, star (φ x) * ψ x).re = 0
    simp only [Complex.neg_re] at hre
    linarith
  · change (∫ x, star (φ x) * ψ x).im = 0
    simp only [Complex.neg_im] at him
    linarith

theorem normalizedParityTrialStates_orthogonal (b L coupling : ℝ) (φ : Wavefunction) :
    waveInner (normalizedParityTrialState true b L coupling φ)
      (normalizedParityTrialState false b L coupling φ) = 0 :=
  waveInner_eq_zero_of_even_odd
    (normalizedParityTrialState_hasParity true b L coupling φ)
    (normalizedParityTrialState_hasParity false b L coupling φ)

theorem contDiff_parityTrialState
    (even : Bool) (b L coupling : ℝ) {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (parityTrialState even b L coupling φ) := by
  have hleft := contDiff_magneticTranslation b coupling (-displacement L) hφ
  have hright := hleft.comp contDiff_id.neg
  cases even
  · exact hleft.sub hright
  · exact hleft.add hright

theorem contDiff_normalizedParityTrialState
    (even : Bool) (b L coupling : ℝ) {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (normalizedParityTrialState even b L coupling φ) :=
  contDiff_const.smul (contDiff_parityTrialState even b L coupling hφ)

end InfiniteZero
