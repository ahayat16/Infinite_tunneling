import InfiniteZero.ComplexLandauHolomorphic

/-!
# Exterior radial square integrability of the Landau kernel

The existing bound `K(r) ≤ 1 / (π E r²)` already implies exterior square
integrability with radial measure `r dr`: the squared integrand is bounded
by a constant times `r⁻³`. No Gaussian estimate or resolvent identification
is needed for this part of P2.4.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace InfiniteZero

theorem continuousAt_landauKernel {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    ContinuousAt (landauKernel b h E) r := by
  have hrC : 0 < ((r : ℂ) ^ 2).re := by
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos hr
  have hc := (differentiableAt_complexLandauKernel hb hh hE hrC).continuousAt
  have hreal := Complex.continuous_re.continuousAt.comp
    (hc.comp Complex.continuous_ofReal.continuousAt)
  simpa only [Function.comp_def, complexLandauKernel_ofReal, Complex.ofReal_re] using hreal

theorem continuousOn_landauKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) :
    ContinuousOn (landauKernel b h E) (Ioi 0) :=
  fun _ hr => (continuousAt_landauKernel hb hh hE hr).continuousWithinAt

/-- The real radial kernel is square integrable outside every positive radius,
with the actual planar radial density `r`. -/
theorem integrableOn_radial_landauKernel_sq {b h E a : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r * ‖landauKernel b h E r‖ ^ 2) (Ioi a) := by
  have hmajor : IntegrableOn
      (fun r : ℝ => (1 / (Real.pi * E)) ^ 2 * r ^ (-3 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) ha).const_mul _
  have hcont : ContinuousOn
      (fun r : ℝ => r * ‖landauKernel b h E r‖ ^ 2) (Ioi a) :=
    (continuousOn_id.mul ((continuousOn_landauKernel hb hh hE).norm.pow 2)).mono
      (fun _ hr => ha.trans hr)
  apply hmajor.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hrpos : 0 < r := ha.trans hr
  have hK : ‖landauKernel b h E r‖ ≤ 1 / (Real.pi * E * r ^ 2) := by
    rw [Real.norm_eq_abs, abs_of_pos (landauKernel_pos hb hh hE hrpos)]
    exact landauKernel_le hb hh hE hrpos
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrpos.le (sq_nonneg _))]
  calc
    r * ‖landauKernel b h E r‖ ^ 2 ≤ r * (1 / (Real.pi * E * r ^ 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hK) hrpos.le
    _ = (1 / (Real.pi * E)) ^ 2 * r ^ (-3 : ℝ) := by
      rw [Real.rpow_neg hrpos.le]
      norm_num only [Real.rpow_ofNat]
      field_simp [hrpos.ne', hE.ne', Real.pi_ne_zero]

end InfiniteZero
