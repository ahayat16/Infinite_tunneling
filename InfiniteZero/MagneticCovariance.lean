import InfiniteZero.MagneticModel
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Covariance of the concrete magnetic differential expression

The phase convention in `magneticTranslation` intertwines every covariant
momentum. Inversion anticommutes with a momentum and commutes with its square.
These are identities for the actual Fréchet derivatives of `MagneticModel`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

private def magneticPhaseLinear (b coupling : ℝ) (a : Plane) : Plane →L[ℝ] ℂ :=
  (-Complex.I) • (Complex.ofRealCLM.comp
    ((b * coupling / 2) •
      (a 1 • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 -
       a 0 • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)))

private theorem magneticPhaseLinear_apply (b coupling : ℝ) (a x : Plane) :
    magneticPhaseLinear b coupling a x =
      -Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ) := by
  simp only [magneticPhaseLinear, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, PiLp.proj_apply,
    smul_eq_mul, Complex.ofRealCLM_apply, wedge]
  congr 2
  ring

private theorem magneticPhaseLinear_coordinate (b coupling : ℝ) (a : Plane) (i : Fin 2) :
    magneticPhaseLinear b coupling a (coordinateVector i) =
      Complex.I * ((b * coupling / 2 * perpCoordinate a i : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [magneticPhaseLinear_apply, coordinateVector, wedge, perpCoordinate,
      Complex.ofReal_mul, Complex.ofReal_neg]

theorem contDiff_magneticTranslation (b coupling : ℝ) (a : Plane) {φ : Wavefunction}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (magneticTranslation b coupling a φ) := by
  have hg : ContDiff ℝ ∞ (fun x => Complex.exp (magneticPhaseLinear b coupling a x)) :=
    (magneticPhaseLinear b coupling a).contDiff.cexp
  simpa only [magneticTranslation, magneticPhaseLinear_apply] using
    hg.mul (hφ.comp (contDiff_id.sub contDiff_const))

theorem contDiff_partialDerivative (i : Fin 2) {φ : Wavefunction}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (partialDerivative i φ) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_perpCoordinate (i : Fin 2) :
    ContDiff ℝ ∞ (fun x : Plane => perpCoordinate x i) := by
  unfold perpCoordinate
  split_ifs
  · exact (contDiff_piLp_apply 2).neg
  · exact contDiff_piLp_apply 2

theorem contDiff_covariantDerivative (b coupling : ℝ) (i : Fin 2) {φ : Wavefunction}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (covariantDerivative b coupling i φ) := by
  exact (contDiff_const.mul (contDiff_partialDerivative i hφ)).sub
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (contDiff_perpCoordinate i))).mul hφ)

theorem partialDerivative_magneticTranslation (b coupling : ℝ) (a : Plane)
    (i : Fin 2) {φ : Wavefunction} (hφ : Differentiable ℝ φ) (x : Plane) :
    partialDerivative i (magneticTranslation b coupling a φ) x =
      Complex.exp (-Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ)) *
        (partialDerivative i φ (x - a) +
          Complex.I * ((b * coupling / 2 * perpCoordinate a i : ℝ) : ℂ) * φ (x - a)) := by
  have hd := ((magneticPhaseLinear b coupling a).hasFDerivAt.cexp).mul
    ((hφ (x - a)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a))
  have he := congrArg (fun f : Plane →L[ℝ] ℂ => f (coordinateVector i)) hd.fderiv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    magneticPhaseLinear_coordinate, Function.comp_apply, id_eq] at he
  simp only [magneticPhaseLinear_apply] at he
  rw [show partialDerivative i (magneticTranslation b coupling a φ) x =
      _ from he]
  simp only [partialDerivative]
  ring

theorem covariantDerivative_magneticTranslation (b coupling : ℝ) (a : Plane)
    (i : Fin 2) {φ : Wavefunction} (hφ : Differentiable ℝ φ) :
    covariantDerivative b coupling i (magneticTranslation b coupling a φ) =
      magneticTranslation b coupling a (covariantDerivative b coupling i φ) := by
  funext x
  have hp : perpCoordinate (x - a) i = perpCoordinate x i - perpCoordinate a i := by
    unfold perpCoordinate
    split_ifs <;> simp only [PiLp.sub_apply]
    ring
  simp only [covariantDerivative, partialDerivative_magneticTranslation b coupling a i hφ,
    magneticTranslation, hp, Complex.ofReal_mul, Complex.ofReal_sub]
  ring_nf
  simp [Complex.I_sq]

theorem magneticHamiltonian_magneticTranslation (b coupling : ℝ) (a : Plane)
    (V : Potential) {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) :
    magneticHamiltonian b coupling (fun x => V (x - a))
        (magneticTranslation b coupling a φ) =
      magneticTranslation b coupling a (magneticHamiltonian b coupling V φ) := by
  have hd := hφ.differentiable (by simp)
  funext x
  simp only [magneticHamiltonian, covariantDerivative_magneticTranslation b coupling a _ hd,
    covariantDerivative_magneticTranslation b coupling a _
      ((contDiff_covariantDerivative b coupling _ hφ).differentiable (by simp)),
    magneticTranslation, ← Finset.mul_sum]
  ring

theorem partialDerivative_inversion (i : Fin 2) {φ : Wavefunction}
    (hφ : Differentiable ℝ φ) (x : Plane) :
    partialDerivative i (fun y => φ (-y)) x = -partialDerivative i φ (-x) := by
  have hd := (hφ (-x)).hasFDerivAt.comp x (hasFDerivAt_id x).neg
  have he := congrArg (fun f : Plane →L[ℝ] ℂ => f (coordinateVector i)) hd.fderiv
  simpa only [partialDerivative, Function.comp_apply, id_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg] using he

theorem covariantDerivative_inversion (b coupling : ℝ) (i : Fin 2)
    {φ : Wavefunction} (hφ : Differentiable ℝ φ) :
    covariantDerivative b coupling i (fun x => φ (-x)) =
      fun x => -covariantDerivative b coupling i φ (-x) := by
  funext x
  have hp : perpCoordinate (-x) i = -perpCoordinate x i := by
    unfold perpCoordinate
    split_ifs <;> simp
  simp only [covariantDerivative, partialDerivative_inversion i hφ, hp,
    mul_neg, Complex.ofReal_neg]
  ring

theorem covariantDerivative_neg (b coupling : ℝ) (i : Fin 2) (φ : Wavefunction) :
    covariantDerivative b coupling i (-φ) = -covariantDerivative b coupling i φ := by
  funext x
  simp only [covariantDerivative, partialDerivative, fderiv_neg,
    ContinuousLinearMap.neg_apply, Pi.neg_apply]
  ring

theorem magneticHamiltonian_inversion (b coupling : ℝ) (V : Potential)
    {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) :
    magneticHamiltonian b coupling (fun x => V (-x)) (fun x => φ (-x)) =
      fun x => magneticHamiltonian b coupling V φ (-x) := by
  have hd := hφ.differentiable (by simp)
  funext x
  have hsecond (i : Fin 2) :
      covariantDerivative b coupling i
        (covariantDerivative b coupling i (fun x => φ (-x))) x =
        covariantDerivative b coupling i (covariantDerivative b coupling i φ) (-x) := by
    rw [covariantDerivative_inversion b coupling i hd]
    change covariantDerivative b coupling i (-(fun y => covariantDerivative b coupling i φ (-y))) x = _
    rw [covariantDerivative_neg, covariantDerivative_inversion b coupling i
      ((contDiff_covariantDerivative b coupling i hφ).differentiable (by simp))]
    simp
  simp only [magneticHamiltonian, hsecond]

theorem norm_magneticTranslation (b coupling : ℝ) (a : Plane) (φ : Wavefunction)
    (x : Plane) : ‖magneticTranslation b coupling a φ x‖ = ‖φ (x - a)‖ := by
  simp [magneticTranslation, Complex.norm_exp, Complex.mul_re]

theorem memLp_magneticTranslation (b coupling : ℝ) (a : Plane) {φ : Wavefunction}
    (hφ : ContDiff ℝ ∞ φ) (hLp : MemLp φ 2 volume) :
    MemLp (magneticTranslation b coupling a φ) 2 volume := by
  apply (hLp.comp_measurePreserving (measurePreserving_sub_right volume a)).congr_norm
    (contDiff_magneticTranslation b coupling a hφ).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (norm_magneticTranslation b coupling a φ x).symm

theorem mass_magneticTranslation (b coupling : ℝ) (a : Plane) (φ : Wavefunction) :
    mass (magneticTranslation b coupling a φ) = mass φ := by
  simp only [mass, norm_magneticTranslation]
  exact integral_sub_right_eq_self (fun x => ‖φ x‖ ^ 2) a

theorem mass_inversion (φ : Wavefunction) : mass (fun x => φ (-x)) = mass φ :=
  integral_neg_eq_self (fun x => ‖φ x‖ ^ 2) volume

theorem IsEigenfunction.magneticTranslated {b coupling E : ℝ} {V : Potential}
    {φ : Wavefunction} (hφ : IsEigenfunction b coupling V E φ) (a : Plane) :
    IsEigenfunction b coupling (fun x => V (x - a)) E
      (magneticTranslation b coupling a φ) := by
  refine ⟨contDiff_magneticTranslation b coupling a hφ.1,
    memLp_magneticTranslation b coupling a hφ.1 hφ.2.1, ?_⟩
  intro x
  rw [magneticHamiltonian_magneticTranslation b coupling a V hφ.1]
  simp only [magneticTranslation, hφ.2.2]
  ring

theorem IsEigenfunction.inversion {b coupling E : ℝ} {V : Potential}
    {φ : Wavefunction} (hφ : IsEigenfunction b coupling V E φ) :
    IsEigenfunction b coupling (fun x => V (-x)) E (fun x => φ (-x)) := by
  refine ⟨hφ.1.comp contDiff_id.neg,
    hφ.2.1.comp_measurePreserving (volume.measurePreserving_neg), ?_⟩
  intro x
  rw [magneticHamiltonian_inversion b coupling V hφ.1]
  exact hφ.2.2 (-x)

theorem doubleHamiltonian_inversion (b L coupling : ℝ) (v : Potential)
    {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) :
    doubleHamiltonian b v L coupling (fun x => φ (-x)) =
      fun x => doubleHamiltonian b v L coupling φ (-x) := by
  simpa only [doubleHamiltonian, doubleWellPotential_inversion] using
    magneticHamiltonian_inversion b coupling (doubleWellPotential v L) hφ

theorem IsDoubleEigenfunction.inversion {b L coupling E : ℝ} {v : Potential}
    {φ : Wavefunction} (hφ : IsDoubleEigenfunction b v L coupling E φ) :
    IsDoubleEigenfunction b v L coupling E (fun x => φ (-x)) := by
  simpa only [doubleWellPotential_inversion] using
    (show IsEigenfunction b coupling (doubleWellPotential v L) E φ from hφ).inversion

theorem IsAtomicGroundState.leftState_eigenfunction {b coupling : ℝ} {v : Potential}
    {φ : Wavefunction} (hφ : IsAtomicGroundState b v coupling φ) (L : ℝ) :
    IsEigenfunction b coupling (fun x => v (x + displacement L))
      (atomicGroundEnergy b v coupling) (leftState b L coupling φ) ∧
      mass (leftState b L coupling φ) = 1 := by
  constructor
  · simpa only [leftState, sub_neg_eq_add] using hφ.1.magneticTranslated (-displacement L)
  · exact (mass_magneticTranslation b coupling (-displacement L) φ).trans hφ.2

theorem IsAtomicGroundState.rightState_eigenfunction {b coupling : ℝ} {v : Potential}
    {φ : Wavefunction} (hφ : IsAtomicGroundState b v coupling φ) (L : ℝ) :
    IsEigenfunction b coupling (fun x => v (displacement L - x))
      (atomicGroundEnergy b v coupling) (rightState b L coupling φ) ∧
      mass (rightState b L coupling φ) = 1 := by
  constructor
  · simpa only [rightState, neg_add_eq_sub] using (hφ.leftState_eigenfunction L).1.inversion
  · exact (mass_inversion (leftState b L coupling φ)).trans (hφ.leftState_eigenfunction L).2

/-- The right mode obeys the free magnetic equation with the translated
potential as an explicit source. This is the differential input needed to
apply a classical free-Landau resolvent theorem. -/
theorem IsAtomicGroundState.rightState_free_equation {b coupling : ℝ} {v : Potential}
    {φ : Wavefunction} (hφ : IsAtomicGroundState b v coupling φ) (L : ℝ) (x : Plane) :
    magneticHamiltonian b coupling 0 (rightState b L coupling φ) x -
      (atomicGroundEnergy b v coupling : ℂ) * rightState b L coupling φ x =
        -((coupling ^ 2 * v (displacement L - x) : ℝ) : ℂ) *
          rightState b L coupling φ x := by
  have he := (hφ.rightState_eigenfunction L).1.2.2 x
  simp only [magneticHamiltonian, Pi.zero_apply, mul_zero, Complex.ofReal_zero,
    zero_mul, add_zero] at he ⊢
  linear_combination he

end InfiniteZero
