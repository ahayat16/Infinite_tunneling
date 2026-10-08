import InfiniteZero.LandauHeatKernel
import InfiniteZero.MagneticRadialReduction
import InfiniteZero.MagneticEllipticExpansion
import InfiniteZero.MagneticTestGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Landau heat equation

The spatial Gaussian calculation and the derivatives of the hyperbolic
amplitude verify the heat equation for the explicit symmetric-gauge kernel.
The equation in the source variable uses magnetic field `-B`.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

private theorem contDiff_gaussian (a : ℝ) :
    ContDiff ℝ ∞ (fun y : Plane => (Real.exp (-a * ‖y‖ ^ 2) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul (contDiff_norm_sq ℝ)).exp)

private theorem gaussian_radial_deriv (a r : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-a * s ^ 2))
      (-2 * a * r * Real.exp (-a * r ^ 2)) r := by
  convert (((hasDerivAt_id r).pow 2).const_mul (-a)).exp using 1
  dsimp
  ring

private theorem gaussian_radial_second (a r : ℝ) :
    HasDerivAt (fun s : ℝ => -2 * a * s * Real.exp (-a * s ^ 2))
      ((-2 * a + 4 * a ^ 2 * r ^ 2) * Real.exp (-a * r ^ 2)) r := by
  convert ((hasDerivAt_id r).const_mul (-2 * a)).mul
    (gaussian_radial_deriv a r) using 1
  dsimp
  ring

/-- The magnetic Laplacian applied to a centered scalar Gaussian. -/
theorem magneticHamiltonian_gaussian (B a : ℝ) (x : Plane) :
    magneticHamiltonian B 1 0 (fun y => (Real.exp (-a * ‖y‖ ^ 2) : ℂ)) x =
      (((4 * a + (B ^ 2 / 4 - 4 * a ^ 2) * ‖x‖ ^ 2) *
        Real.exp (-a * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  have hg := contDiff_gaussian a
  have hcont : Continuous
      (magneticHamiltonian B 1 0 (fun y => (Real.exp (-a * ‖y‖ ^ 2) : ℂ))) := by
    unfold magneticHamiltonian
    apply Continuous.add
    · exact continuous_finsetSum _ fun i _ =>
        (contDiff_covariantDerivative B 1 i
          (contDiff_covariantDerivative B 1 i hg)).continuous
    · simp only [Pi.zero_apply, mul_zero, Complex.ofReal_zero, zero_mul]
      exact continuous_const
  have heq := Continuous.ext_on (dense_compl_singleton (0 : Plane)) hcont
    (show Continuous (fun x : Plane =>
      (((4 * a + (B ^ 2 / 4 - 4 * a ^ 2) * ‖x‖ ^ 2) *
        Real.exp (-a * ‖x‖ ^ 2) : ℝ) : ℂ)) by fun_prop) (by
      intro y hy
      have hy0 : y ≠ 0 := hy
      rw [magneticHamiltonian_radial (fun r _ => gaussian_radial_deriv a r) hy0
        (gaussian_radial_second a ‖y‖) B 1 0]
      congr 1
      simp only [one_pow, mul_one, Pi.zero_apply, mul_zero, add_zero]
      field_simp [norm_ne_zero_iff.mpr hy0]
      ring)
  exact congrFun heq x

/-- The source-variable heat kernel is a magnetic translate of a centered
Gaussian, with the reversed field required by the source convention. -/
theorem landauHeatKernel_eq_magneticTranslation (B t : ℝ) (x : Plane) :
    landauHeatKernel B t x = magneticTranslation (-B) 1 x
      ((landauHeatAmplitude B t : ℂ) •
        (fun y => (Real.exp (-landauHeatRate B t * ‖y‖ ^ 2) : ℂ))) := by
  ext y
  have hp : -B * 1 / 2 * wedge y x = B / 2 * wedge x y := by
    unfold wedge
    ring
  simp only [landauHeatKernel, magneticTranslation, hp, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_mul, norm_sub_rev y x]
  ring

/-- For every positive time the heat kernel is smooth in its source variable. -/
theorem contDiff_landauHeatKernel_source (B t : ℝ) (x : Plane) :
    ContDiff ℝ ∞ (landauHeatKernel B t x) := by
  rw [landauHeatKernel_eq_magneticTranslation]
  apply contDiff_magneticTranslation
  simpa only [Pi.smul_def] using
    (contDiff_gaussian (landauHeatRate B t)).const_smul (landauHeatAmplitude B t : ℂ)

/-- Spatial differentiation of the explicit heat kernel. -/
theorem magneticHamiltonian_landauHeatKernel_source (B t : ℝ) (x y : Plane) :
    magneticHamiltonian (-B) 1 0 (landauHeatKernel B t x) y =
      ((4 * landauHeatRate B t +
        (B ^ 2 / 4 - 4 * landauHeatRate B t ^ 2) * ‖x - y‖ ^ 2 : ℝ) : ℂ) *
        landauHeatKernel B t x y := by
  rw [landauHeatKernel_eq_magneticTranslation B t x]
  have hg : ContDiff ℝ ∞ ((landauHeatAmplitude B t : ℂ) •
      (fun y : Plane => (Real.exp (-landauHeatRate B t * ‖y‖ ^ 2) : ℂ))) := by
    simpa only [Pi.smul_def] using
      (contDiff_gaussian (landauHeatRate B t)).const_smul (landauHeatAmplitude B t : ℂ)
  have hcov := magneticHamiltonian_magneticTranslation (-B) 1 x 0 hg
  change magneticHamiltonian (-B) 1 (fun y : Plane => (0 : Potential) (y - x)) _ y = _
  rw [hcov, magneticHamiltonian_smul _ _ _ (contDiff_gaussian _)]
  simp only [magneticTranslation, Pi.smul_apply, smul_eq_mul,
    magneticHamiltonian_gaussian, neg_sq, norm_sub_rev y x,
    Complex.ofReal_mul]
  ring

/-- The hyperbolic Gaussian rate solves its scalar Riccati equation. -/
theorem hasDerivAt_landauHeatRate {B t : ℝ} (h : Real.sinh (B * t) ≠ 0) :
    HasDerivAt (landauHeatRate B)
      (B ^ 2 / 4 - 4 * landauHeatRate B t ^ 2) t := by
  have hs := ((hasDerivAt_id t).const_mul B).sinh
  have hc := ((hasDerivAt_id t).const_mul B).cosh
  convert (hc.div hs h).const_mul (B / 4) using 1
  dsimp only [landauHeatRate, id_eq]
  field_simp

/-- The derivative of the heat amplitude in terms of its Gaussian rate. -/
theorem hasDerivAt_landauHeatAmplitude {B t : ℝ} (h : Real.sinh (B * t) ≠ 0) :
    HasDerivAt (landauHeatAmplitude B)
      (-4 * landauHeatRate B t * landauHeatAmplitude B t) t := by
  have hs := (((hasDerivAt_id t).const_mul B).sinh).const_mul (4 * Real.pi)
  convert (hasDerivAt_const t B).div hs (mul_ne_zero (by positivity) h) using 1
  dsimp only [landauHeatRate, landauHeatAmplitude, id_eq]
  field_simp
  ring

/-- The source-variable heat equation, with a classical derivative in time. -/
theorem hasDerivAt_landauHeatKernel {B t : ℝ} (hB : 0 < B) (ht : 0 < t)
    (x y : Plane) :
    HasDerivAt (fun s => landauHeatKernel B s x y)
      (-(magneticHamiltonian (-B) 1 0 (landauHeatKernel B t x) y)) t := by
  have h := (Real.sinh_pos_iff.mpr (mul_pos hB ht)).ne'
  have hd := ((hasDerivAt_landauHeatAmplitude h).mul
    (((hasDerivAt_landauHeatRate h).neg.mul_const (‖x - y‖ ^ 2)).exp)).ofReal_comp
  convert hd.mul_const
    (Complex.exp (-Complex.I * ((B / 2 * wedge x y : ℝ) : ℂ))) using 1
  rw [magneticHamiltonian_landauHeatKernel_source]
  simp only [landauHeatKernel, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_sub, Pi.neg_apply]
  push_cast
  ring

/-- Joint continuity in positive time and source position. -/
theorem continuousOn_landauHeatKernel_time_source {B : ℝ} (hB : 0 < B) (x : Plane) :
    ContinuousOn (fun q : ℝ × Plane => landauHeatKernel B q.1 x q.2)
      {q | 0 < q.1} := by
  intro q hq
  have hs : Real.sinh (B * q.1) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hB hq)).ne'
  have hd : 4 * Real.pi * Real.sinh (B * q.1) ≠ 0 :=
    mul_ne_zero (by positivity) hs
  apply ContinuousAt.continuousWithinAt
  unfold landauHeatKernel landauHeatAmplitude landauHeatRate wedge
  fun_prop (disch := assumption)

/-- Joint continuity of the source-side Hamiltonian of the heat kernel. -/
theorem continuousOn_magneticHamiltonian_landauHeatKernel_source {B : ℝ}
    (hB : 0 < B) (x : Plane) :
    ContinuousOn (fun q : ℝ × Plane =>
      magneticHamiltonian (-B) 1 0 (landauHeatKernel B q.1 x) q.2)
      {q | 0 < q.1} := by
  simp_rw [magneticHamiltonian_landauHeatKernel_source]
  intro q hq
  have hs : Real.sinh (B * q.1) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hB hq)).ne'
  have hd : 4 * Real.pi * Real.sinh (B * q.1) ≠ 0 :=
    mul_ne_zero (by positivity) hs
  apply ContinuousAt.continuousWithinAt
  unfold landauHeatKernel landauHeatAmplitude landauHeatRate wedge
  fun_prop (disch := assumption)

end InfiniteZero
