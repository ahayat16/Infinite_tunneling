import InfiniteZero.LandauKernel
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Proper-time Landau integral for a complex radius

The real part of the bilinear square determines the exact absolute value of
the integrand. This gives convergence and bounds by the real scalar kernel;
no operator identification or holomorphic asymptotic is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def complexLandauIntegrand (b h E : ℝ) (r : ℂ) (τ : ℝ) : ℂ :=
  ((Real.sinh (b * τ) : ℝ) : ℂ)⁻¹ * Complex.exp
    (-((E * τ : ℝ) + (b / 4 : ℝ) * r ^ 2 *
      ((Real.cosh (b * τ) / Real.sinh (b * τ) : ℝ) : ℂ)) / (h : ℂ))

def complexLandauKernel (b h E : ℝ) (r : ℂ) : ℂ :=
  ((b / (4 * Real.pi * h ^ 2) : ℝ) : ℂ) *
    ∫ τ in Ioi (0 : ℝ), complexLandauIntegrand b h E r τ

def complexLandauEffectiveRadius (r : ℂ) : ℝ := Real.sqrt (r ^ 2).re

@[simp] theorem complexLandauIntegrand_ofReal (b h E r τ : ℝ) :
    complexLandauIntegrand b h E (r : ℂ) τ = (landauIntegrand b h E r τ : ℂ) := by
  unfold complexLandauIntegrand landauIntegrand properTimePhase
  push_cast
  congr 2
  ring

@[simp] theorem complexLandauKernel_ofReal (b h E r : ℝ) :
    complexLandauKernel b h E (r : ℂ) = (landauKernel b h E r : ℂ) := by
  unfold complexLandauKernel landauKernel
  simp only [complexLandauIntegrand_ofReal, integral_complex_ofReal, Complex.ofReal_mul]

theorem complexLandauEffectiveRadius_pos {r : ℂ} (hr : 0 < (r ^ 2).re) :
    0 < complexLandauEffectiveRadius r := Real.sqrt_pos.mpr hr

/-- The identity of norms is exact, not merely an exponential majorization. -/
theorem norm_complexLandauIntegrand {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    (h E : ℝ) {r : ℂ} (hr : 0 ≤ (r ^ 2).re) :
    ‖complexLandauIntegrand b h E r τ‖ =
      landauIntegrand b h E (complexLandauEffectiveRadius r) τ := by
  have hs : 0 < Real.sinh (b * τ) := Real.sinh_pos_iff.mpr (mul_pos hb hτ)
  unfold complexLandauIntegrand landauIntegrand properTimePhase complexLandauEffectiveRadius
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le, Complex.norm_exp]
  congr 1
  congr 1
  rw [Real.sq_sqrt hr]
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.neg_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ring

theorem continuousOn_complexLandauIntegrand {b : ℝ} (hb : 0 < b)
    (h E : ℝ) (r : ℂ) :
    ContinuousOn (complexLandauIntegrand b h E r) (Ioi 0) := by
  intro τ hτ
  apply ContinuousAt.continuousWithinAt
  have hs : Real.sinh (b * τ) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hb hτ)).ne'
  have hc : ((Real.sinh (b * τ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  unfold complexLandauIntegrand
  fun_prop

theorem integrableOn_complexLandauIntegrand {b h E : ℝ} {r : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < (r ^ 2).re) :
    IntegrableOn (complexLandauIntegrand b h E r) (Ioi 0) := by
  apply (integrableOn_landauIntegrand hb hh hE (complexLandauEffectiveRadius_pos hr)).mono'
    ((continuousOn_complexLandauIntegrand hb h E r).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  exact (norm_complexLandauIntegrand hb hτ h E hr.le).le

theorem integrableOn_complexLandauIntegrand_subset {b h E : ℝ} {r : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < (r ^ 2).re)
    {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    IntegrableOn (complexLandauIntegrand b h E r) S :=
  (integrableOn_complexLandauIntegrand hb hh hE hr).mono_set hS

/-- Every measurable restriction to positive proper times has the same real
majorant. No positivity of the complex integral is assumed. -/
theorem norm_setIntegral_complexLandauIntegrand_le {b h E : ℝ} {r : ℂ}
    (hb : 0 < b) (hr : 0 ≤ (r ^ 2).re) {S : Set ℝ}
    (hS : MeasurableSet S) (hSpos : S ⊆ Ioi 0) :
    ‖∫ τ in S, complexLandauIntegrand b h E r τ‖ ≤
      ∫ τ in S, landauIntegrand b h E (complexLandauEffectiveRadius r) τ := by
  calc
    _ ≤ ∫ τ in S, ‖complexLandauIntegrand b h E r τ‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hS] with τ hτ
      exact norm_complexLandauIntegrand hb (hSpos hτ) h E hr

theorem norm_complexLandauKernel_le {b h E : ℝ} {r : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hr : 0 ≤ (r ^ 2).re) :
    ‖complexLandauKernel b h E r‖ ≤ landauKernel b h E (complexLandauEffectiveRadius r) := by
  unfold complexLandauKernel landauKernel
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (norm_setIntegral_complexLandauIntegrand_le hb hr measurableSet_Ioi Subset.rfl)
    (by positivity)

end InfiniteZero
