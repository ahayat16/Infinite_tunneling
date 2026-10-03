import InfiniteZero.AffineScaleJets
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Exact planar local integral rescaling

Lebesgue measure transforms by the square of the dilation factor. The
identities hold for the Bochner integral without extra integrability inputs;
continuous functions are integrable on the bounded balls used here.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped Pointwise

namespace InfiniteZero

theorem setIntegral_affineScale_ball (g : Plane → ℝ) (x₀ : Plane)
    {h : ℝ} (hh : 0 < h) (r : ℝ) :
    (∫ y in ball (0 : Plane) r, g (affineScale x₀ h y)) =
      (h ^ 2)⁻¹ * ∫ x in ball x₀ (h * r), g x := by
  change (∫ y in ball (0 : Plane) r, (fun z => g (x₀ + z)) (h • y)) = _
  rw [Measure.setIntegral_comp_smul_of_pos (volume : Measure Plane)
      (fun z : Plane => g (x₀ + z)) (ball (0 : Plane) r) hh,
    _root_.smul_ball hh.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hh]
  simp only [Plane, finrank_euclideanSpace_fin, smul_eq_mul]
  congr 1
  have ht := (measurePreserving_add_left (volume : Measure Plane) x₀).setIntegral_preimage_emb
    (Homeomorph.addLeft x₀).toMeasurableEquiv.measurableEmbedding g (ball x₀ (h * r))
  simpa only [preimage_add_ball, sub_self] using ht

theorem setIntegral_norm_sq_affineScale_ball (f : Wavefunction) (x₀ : Plane)
    {h : ℝ} (hh : 0 < h) (r : ℝ) :
    (∫ y in ball (0 : Plane) r, ‖f (affineScale x₀ h y)‖ ^ 2) =
      (h ^ 2)⁻¹ * ∫ x in ball x₀ (h * r), ‖f x‖ ^ 2 :=
  setIntegral_affineScale_ball (fun x => ‖f x‖ ^ 2) x₀ hh r

theorem setIntegral_norm_sq_affineScale_ball_two (f : Wavefunction) (x₀ : Plane)
    {h : ℝ} (hh : 0 < h) :
    (∫ y in ball (0 : Plane) 2, ‖f (affineScale x₀ h y)‖ ^ 2) =
      (h⁻¹) ^ 2 * ∫ x in ball x₀ (2 * h), ‖f x‖ ^ 2 := by
  simpa only [inv_pow, mul_comm h 2] using
    setIntegral_norm_sq_affineScale_ball f x₀ hh 2

theorem integrableOn_norm_sq_affineScale_ball {f : Wavefunction} (hf : Continuous f)
    (x₀ : Plane) (h r : ℝ) :
    IntegrableOn (fun y => ‖f (affineScale x₀ h y)‖ ^ 2) (ball (0 : Plane) r) := by
  have hc : Continuous (fun y => ‖f (affineScale x₀ h y)‖ ^ 2) :=
    (hf.comp (contDiff_affineScale x₀ h).continuous).norm.pow 2
  exact (hc.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Plane) r)).mono_set ball_subset_closedBall

theorem sqrt_setIntegral_norm_sq_affineScale_ball_two (f : Wavefunction) (x₀ : Plane)
    {h : ℝ} (hh : 0 < h) :
    Real.sqrt (∫ y in ball (0 : Plane) 2, ‖f (affineScale x₀ h y)‖ ^ 2) =
      h⁻¹ * Real.sqrt (∫ x in ball x₀ (2 * h), ‖f x‖ ^ 2) := by
  rw [setIntegral_norm_sq_affineScale_ball_two f x₀ hh,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hh.le)]

end InfiniteZero
