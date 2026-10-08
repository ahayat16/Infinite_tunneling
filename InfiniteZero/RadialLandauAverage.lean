import InfiniteZero.LandauExteriorConvolution
import InfiniteZero.RadialPlaneL2
import InfiniteZero.RealRadialState
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The exact radial convolution through the angular Landau average

The kernel and its magnetic phase are unchanged. Cartesian coordinates
preserve physical volume, polar coordinates contribute the Jacobian r,
and Fubini is justified by the compact source separated from the exterior
evaluation point. No angular positivity or radial factorization is asserted.
-/

noncomputable section
open Set MeasureTheory
open InfiniteZero.CuspParameters

namespace InfiniteZero

/-- Angular average of the genuine free Landau kernel. -/
def radialFreeLandauAverage (b h E R s : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ θ in Ioo (-Real.pi) Real.pi,
      freeLandauKernel b h E (R • coordinateVector 0)
        (planeCartesianEquiv.symm (polarCoord.symm (s, θ)))

theorem two_pi_mul_radialFreeLandauAverage (b h E R s : ℝ) :
    ((2 * Real.pi : ℝ) : ℂ) * radialFreeLandauAverage b h E R s =
      ∫ θ in Ioo (-Real.pi) Real.pi,
        freeLandauKernel b h E (R • coordinateVector 0)
          (planeCartesianEquiv.symm (polarCoord.symm (s, θ))) := by
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) Real.pi_pos).ne'
  rw [radialFreeLandauAverage, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]

private theorem integrable_polar_plane {G : Plane → ℂ} (hG : Integrable G) :
    Integrable (fun q : ℝ × ℝ => (q.1 : ℂ) *
      G (planeCartesianEquiv.symm (polarCoord.symm q)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  have hcart := planeCartesianEquiv_symm_measurePreserving.integrable_comp_of_integrable hG
  have hraw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun q _ => (hasFDerivAt_polarCoord_symm q).hasFDerivWithinAt)
    polarCoord.symm.injOn (fun q => G (planeCartesianEquiv.symm q))).mp hcart.integrableOn
  have hp : IntegrableOn (fun q : ℝ × ℝ => (q.1 : ℂ) *
      G (planeCartesianEquiv.symm (polarCoord.symm q))) polarCoord.target := by
    apply hraw.congr_fun _ polarCoord.open_target.measurableSet
    intro q hq
    have hr : 0 < q.1 := hq.1
    simp only [det_fderivPolarCoordSymm, abs_of_pos hr, Complex.real_smul]
  change Integrable _ ((volume : Measure (ℝ × ℝ)).restrict
    ((Ioi (0 : ℝ)) ×ˢ Ioo (-Real.pi) Real.pi)) at hp
  rwa [Measure.volume_eq_prod, ← Measure.prod_restrict] at hp

private theorem integral_plane_polar {G : Plane → ℂ} (hG : Integrable G) :
    (∫ y : Plane, G y) = ∫ s in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
      (s : ℂ) * G (planeCartesianEquiv.symm (polarCoord.symm (s, θ))) := by
  calc
    (∫ y : Plane, G y) = ∫ q : ℝ × ℝ, G (planeCartesianEquiv.symm q) :=
      (planeCartesianEquiv_symm_measurePreserving.integral_comp
        planeCartesianEquiv.symm.toHomeomorph.measurableEmbedding G).symm
    _ = ∫ q in polarCoord.target,
        q.1 • G (planeCartesianEquiv.symm (polarCoord.symm q)) :=
      (integral_comp_polarCoord_symm (fun q => G (planeCartesianEquiv.symm q))).symm
    _ = _ := by
      simp only [Complex.real_smul]
      change (∫ q in (Ioi (0 : ℝ)) ×ˢ Ioo (-Real.pi) Real.pi,
        (q.1 : ℂ) * G (planeCartesianEquiv.symm (polarCoord.symm q))) = _
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact integral_prod _ (integrable_polar_plane hG)

private theorem angular_radialSource_eq (b h E R : ℝ) (η : ℝ → ℂ)
    {s : ℝ} (hs : 0 < s) :
    (∫ θ in Ioo (-Real.pi) Real.pi, (s : ℂ) *
      (freeLandauKernel b h E (R • coordinateVector 0)
        (planeCartesianEquiv.symm (polarCoord.symm (s, θ))) *
        η ‖planeCartesianEquiv.symm (polarCoord.symm (s, θ))‖)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((s : ℂ) * radialFreeLandauAverage b h E R s * η s) := by
  simp only [norm_planeCartesianEquiv_symm_polarCoord, abs_of_pos hs]
  rw [integral_const_mul, integral_mul_const]
  rw [show ((2 * Real.pi : ℝ) : ℂ) *
      ((s : ℂ) * radialFreeLandauAverage b h E R s * η s) =
      (s : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * radialFreeLandauAverage b h E R s) * η s
    by ring, two_pi_mul_radialFreeLandauAverage]
  ring

/-- Absolute integrability of the averaged radial source follows from the
genuine exterior convolution, not from an additional radial assumption. -/
theorem integrableOn_radialFreeLandauAverage_mul
    {b h E a R : ℝ} {η : ℝ → ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (ha : 0 < a) (hRa : a < R)
    (hη : Continuous (fun y : Plane => η ‖y‖))
    (hs : Function.support (fun y : Plane => η ‖y‖) ⊆ Metric.closedBall (0 : Plane) a) :
    IntegrableOn (fun s : ℝ => (s : ℂ) * radialFreeLandauAverage b h E R s * η s)
      (Ioi 0) := by
  have hx : a < ‖R • coordinateVector 0‖ := by
    rwa [norm_radial_axis (ha.trans hRa).le]
  have hG := integrable_freeLandauKernel_mul_of_support_subset_closedBall hb hh hE hη hs hx
  have hi := (integrable_polar_plane hG).integral_prod_left
  have hj : IntegrableOn (fun s : ℝ => ((2 * Real.pi : ℝ) : ℂ) *
      ((s : ℂ) * radialFreeLandauAverage b h E R s * η s)) (Ioi 0) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact angular_radialSource_eq b h E R η hs
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) Real.pi_pos).ne'
  simpa only [← mul_assoc, inv_mul_cancel₀ hπ, one_mul] using
    hj.const_mul (((2 * Real.pi : ℝ) : ℂ)⁻¹)

/-- Exact polar convolution formula with the physical Lebesgue measure.
The support hypothesis supplies all integrability needed for Fubini. -/
theorem integral_freeLandauKernel_radial_eq_average
    {b h E a R : ℝ} {η : ℝ → ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (ha : 0 < a) (hRa : a < R)
    (hη : Continuous (fun y : Plane => η ‖y‖))
    (hs : Function.support (fun y : Plane => η ‖y‖) ⊆ Metric.closedBall (0 : Plane) a) :
    (∫ y : Plane, freeLandauKernel b h E (R • coordinateVector 0) y * η ‖y‖) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ∫ s in Ioi (0 : ℝ), (s : ℂ) * radialFreeLandauAverage b h E R s * η s := by
  have hx : a < ‖R • coordinateVector 0‖ := by
    rwa [norm_radial_axis (ha.trans hRa).le]
  have hG := integrable_freeLandauKernel_mul_of_support_subset_closedBall hb hh hE hη hs hx
  rw [integral_plane_polar hG, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => angular_radialSource_eq b h E R η hs)

end InfiniteZero
