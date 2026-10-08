import InfiniteZero.LandauHeatKernelBounds
import InfiniteZero.LandauHeatLaplace

/-!
# Absolute integrability of the heat-kernel Laplace transform

The spatial Gaussian mass is bounded by one. Its product with
`exp(-ρt)` is integrable for positive `ρ`, which justifies exchanging time
and space integrals, including for bounded continuous sources.
-/
noncomputable section
open MeasureTheory Set
namespace InfiniteZero

private theorem measurable_heatLaplace (B ρ : ℝ) (x : Plane) :
    Measurable (fun q : ℝ × Plane =>
      (Real.exp (-ρ * q.1) : ℂ) * landauHeatKernel B q.1 x q.2) := by
  exact (show Measurable (fun q : ℝ × Plane => (Real.exp (-ρ * q.1) : ℂ)) by
    fun_prop).mul (measurable_landauHeatKernel_time_right B x)

theorem integral_norm_heatLaplace_spatial_le {B t : ℝ} (hB : 0 < B) (ht : 0 < t)
    (ρ : ℝ) (x : Plane) :
    (∫ y : Plane, ‖(Real.exp (-ρ * t) : ℂ) * landauHeatKernel B t x y‖) ≤
      Real.exp (-ρ * t) := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [integral_const_mul]
  simpa using mul_le_mul_of_nonneg_left (integral_norm_landauHeatKernel_le_one hB ht x)
    (Real.exp_pos (-ρ * t)).le

/-- The exponentially weighted heat kernel is integrable jointly in
positive time and the source point. -/
theorem integrable_heatLaplace_timeSpace {B ρ : ℝ} (hB : 0 < B) (hρ : 0 < ρ) (x : Plane) :
    Integrable (fun q : ℝ × Plane =>
      (Real.exp (-ρ * q.1) : ℂ) * landauHeatKernel B q.1 x q.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hm := measurable_heatLaplace B ρ x
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (integrable_landauHeatKernel_right hB ht x).const_mul _
  · apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hρ) 0).mono'
      hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact integral_norm_heatLaplace_spatial_le hB ht ρ x

/-- The joint absolute integral is bounded by `1/ρ`. -/
theorem integral_norm_heatLaplace_timeSpace_le {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (x : Plane) :
    (∫ q : ℝ × Plane,
      ‖(Real.exp (-ρ * q.1) : ℂ) * landauHeatKernel B q.1 x q.2‖
      ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) ≤ 1 / ρ := by
  have hi := integrable_heatLaplace_timeSpace hB hρ x
  rw [integral_prod _ hi.norm]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-ρ * t) := by
      apply integral_mono_ae hi.integral_norm_prod_left
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos hρ) 0)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact integral_norm_heatLaplace_spatial_le hB ht ρ x
    _ = 1 / ρ := by rw [integral_exp_mul_Ioi (neg_neg_of_pos hρ)]; simp

/-- Bounded continuous sources preserve joint absolute integrability. -/
theorem integrable_heatLaplace_source_timeSpace {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (x : Plane) {f : Wavefunction}
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    Integrable (fun q : ℝ × Plane =>
      ((Real.exp (-ρ * q.1) : ℂ) * landauHeatKernel B q.1 x q.2) * f q.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hi := integrable_heatLaplace_timeSpace hB hρ x
  apply (hi.norm.mul_const M).mono'
    ((measurable_heatLaplace B ρ x).mul (hf.measurable.comp measurable_snd)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM q.2) (norm_nonneg _)

/-- Every spatial row of the standard resolvent kernel is integrable. -/
theorem integrable_freeLandauKernel_standard {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (x : Plane) :
    Integrable (freeLandauKernel B 1 ρ x) := by
  simpa only [← freeLandauKernel_eq_heatLaplace] using
    (integrable_heatLaplace_timeSpace hB hρ x).integral_prod_right

/-- The spatial absolute mass of the standard resolvent is at most `1/ρ`. -/
theorem integral_norm_freeLandauKernel_standard_le {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (x : Plane) :
    (∫ y : Plane, ‖freeLandauKernel B 1 ρ x y‖) ≤ 1 / ρ := by
  have hi := integrable_heatLaplace_timeSpace hB hρ x
  calc
    _ ≤ ∫ y : Plane, ∫ t in Ioi (0 : ℝ),
        ‖(Real.exp (-ρ * t) : ℂ) * landauHeatKernel B t x y‖ := by
      apply integral_mono (integrable_freeLandauKernel_standard hB hρ x).norm
        hi.integral_norm_prod_right
      intro y
      change ‖freeLandauKernel B 1 ρ x y‖ ≤ _
      rw [freeLandauKernel_eq_heatLaplace]
      exact norm_integral_le_integral_norm _
    _ = ∫ q : ℝ × Plane,
        ‖(Real.exp (-ρ * q.1) : ℂ) * landauHeatKernel B q.1 x q.2‖
        ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := (integral_prod_symm _ hi.norm).symm
    _ ≤ 1 / ρ := integral_norm_heatLaplace_timeSpace_le hB hρ x

end InfiniteZero
