import InfiniteZero.LandauHeatKernel
import InfiniteZero.PlaneGaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Spatial mass bounds for the magnetic Gaussian

The magnetic phase has modulus one. Gaussian integration gives the exact
mass `1 / cosh(Bt)`, hence a bound by one independent of time and position.
-/
noncomputable section
open MeasureTheory Set
namespace InfiniteZero

theorem continuous_landauHeatKernel_right (B t : ℝ) (x : Plane) :
    Continuous (landauHeatKernel B t x) := by
  unfold landauHeatKernel wedge
  fun_prop

theorem measurable_landauHeatKernel_time_right (B : ℝ) (x : Plane) :
    Measurable (fun q : ℝ × Plane => landauHeatKernel B q.1 x q.2) := by
  unfold landauHeatKernel landauHeatAmplitude landauHeatRate wedge
  fun_prop

theorem landauHeatKernel_norm {B t : ℝ} (hB : 0 < B) (ht : 0 < t) (x y : Plane) :
    ‖landauHeatKernel B t x y‖ =
      landauHeatAmplitude B t * Real.exp (-landauHeatRate B t * ‖x - y‖ ^ 2) := by
  simp only [landauHeatKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (landauHeatAmplitude_pos hB ht), abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  simp

theorem integrable_norm_landauHeatKernel_right {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) (x : Plane) :
    Integrable (fun y => ‖landauHeatKernel B t x y‖) := by
  simp_rw [landauHeatKernel_norm hB ht]
  exact (integrable_planeGaussian_sub (landauHeatRate_pos hB ht) x).const_mul _

theorem integrable_landauHeatKernel_right {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) (x : Plane) :
    Integrable (landauHeatKernel B t x) :=
  (integrable_norm_iff (continuous_landauHeatKernel_right B t x).aestronglyMeasurable).mp
    (integrable_norm_landauHeatKernel_right hB ht x)

theorem landauHeatAmplitude_mul_gaussianMass {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) :
    landauHeatAmplitude B t * (Real.pi / landauHeatRate B t) =
      1 / Real.cosh (B * t) := by
  have hs := (Real.sinh_pos_iff.mpr (mul_pos hB ht)).ne'
  have hc := (Real.cosh_pos (B * t)).ne'
  unfold landauHeatAmplitude landauHeatRate
  field_simp [hB.ne', hs, hc, Real.pi_ne_zero]


theorem integral_norm_landauHeatKernel_right {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) (x : Plane) :
    (∫ y : Plane, ‖landauHeatKernel B t x y‖) = 1 / Real.cosh (B * t) := by
  simp_rw [landauHeatKernel_norm hB ht]
  rw [integral_const_mul, integral_planeGaussian_sub (landauHeatRate_pos hB ht),
    landauHeatAmplitude_mul_gaussianMass hB ht]

theorem landauHeatKernel_norm_swap {B t : ℝ} (hB : 0 < B) (ht : 0 < t) (x y : Plane) :
    ‖landauHeatKernel B t x y‖ = ‖landauHeatKernel B t y x‖ := by
  simp only [landauHeatKernel_norm hB ht, norm_sub_rev]

theorem integral_norm_landauHeatKernel_left {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) (y : Plane) :
    (∫ x : Plane, ‖landauHeatKernel B t x y‖) = 1 / Real.cosh (B * t) := by
  simp_rw [landauHeatKernel_norm_swap hB ht _ y]
  exact integral_norm_landauHeatKernel_right hB ht y

theorem integral_norm_landauHeatKernel_le_one {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) (x : Plane) :
    (∫ y : Plane, ‖landauHeatKernel B t x y‖) ≤ 1 := by
  rw [integral_norm_landauHeatKernel_right hB ht]
  exact (div_le_one (Real.cosh_pos _)).mpr (Real.one_le_cosh _)

theorem integrable_landauHeatKernel_mul_bounded {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) (x : Plane) {f : Wavefunction}
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    Integrable (fun y => landauHeatKernel B t x y * f y) := by
  apply ((integrable_norm_landauHeatKernel_right hB ht x).mul_const M).mono'
    ((continuous_landauHeatKernel_right B t x).mul hf).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖landauHeatKernel B t x y * f y‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)

theorem integral_norm_landauHeatKernel_mul_bounded_le {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) (x : Plane) {f : Wavefunction}
    (hf : Continuous f) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, ‖f y‖ ≤ M) :
    (∫ y : Plane, ‖landauHeatKernel B t x y * f y‖) ≤ M := by
  calc
    _ ≤ ∫ y : Plane, ‖landauHeatKernel B t x y‖ * M :=
      integral_mono (integrable_landauHeatKernel_mul_bounded hB ht x hf hM).norm
        ((integrable_norm_landauHeatKernel_right hB ht x).mul_const M)
        (fun y => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _))
    _ = (∫ y : Plane, ‖landauHeatKernel B t x y‖) * M := integral_mul_const _ _
    _ ≤ M := by
      simpa using mul_le_mul_of_nonneg_right
        (integral_norm_landauHeatKernel_le_one hB ht x) hM0

end InfiniteZero
