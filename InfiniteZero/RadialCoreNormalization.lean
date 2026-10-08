import InfiniteZero.RadialCoreSourceRepresentation
import InfiniteZero.RadialLandauAverage
import InfiniteZero.CoreRadialHypotheses

/-!
# Exact normalization of the exterior radial core coefficient

The regular profile is the real part of the angular average divided by the
positive exterior radial kernel. Its value at zero is one. Polar integration
of the true source equation gives an exact integral for any coefficient `Γ`
representing the same state at the chosen exterior radius. Positivity or a
lower bound for the regular profile is not assumed or asserted here.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

open CuspParameters

def regularLandauProfile (b h E R s : ℝ) : ℝ :=
  (radialFreeLandauAverage b h E R s).re / landauKernel b h E R

theorem radialFreeLandauAverage_zero (b h E : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    radialFreeLandauAverage b h E R 0 = (landauKernel b h E R : ℂ) := by
  have hy (θ : ℝ) : planeCartesianEquiv.symm (polarCoord.symm (0, θ)) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_planeCartesianEquiv_symm_polarCoord]
    simp
  have hk (θ : ℝ) : freeLandauKernel b h E (R • coordinateVector 0)
      (planeCartesianEquiv.symm (polarCoord.symm (0, θ))) =
      (landauKernel b h E R : ℂ) := by
    rw [hy]
    simp [freeLandauKernel, wedge, norm_radial_axis hR]
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) Real.pi_pos).ne'
  simp only [radialFreeLandauAverage, hk, setIntegral_const, Real.volume_real_Ioo,
    sub_neg_eq_add, show Real.pi + Real.pi = 2 * Real.pi by ring,
    max_eq_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le), Complex.real_smul]
  rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

theorem regularLandauProfile_zero {b h E R : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hR : 0 < R) :
    regularLandauProfile b h E R 0 = 1 := by
  rw [regularLandauProfile, radialFreeLandauAverage_zero b h E hR.le,
    Complex.ofReal_re, div_self (landauKernel_pos hb hh hE hR).ne']

private theorem coreRadialSource_eq {p : CuspParameters} {φ : Wavefunction}
    (hpos : IsPositiveRadial φ) :
    (fun y : Plane => ((-p.coreRadialProfile ‖y‖ * realRadialProfile φ ‖y‖ : ℝ) : ℂ)) =
      coreResolventSource p φ := by
  funext y
  dsimp only [coreResolventSource]
  rw [p.core_eq_coreRadialProfile_norm y, hpos.radial y]
  push_cast
  rfl

/-- Absolute integrability is inherited from the complex polar convolution,
including at large radius where the source vanishes. -/
theorem integrableOn_regularLandauProfile_core_source
    {b h E R : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < p.r₀) (hR : p.r₀ < R)
    (hφ : ContDiff ℝ ∞ φ) (hpos : IsPositiveRadial φ) :
    IntegrableOn (fun s : ℝ => s * regularLandauProfile b h E R s *
      (-p.coreRadialProfile s) * realRadialProfile φ s) (Ioi 0) := by
  let η : ℝ → ℂ := fun s => ((-p.coreRadialProfile s * realRadialProfile φ s : ℝ) : ℂ)
  have heq : (fun y : Plane => η ‖y‖) = coreResolventSource p φ := coreRadialSource_eq hpos
  have hη : Continuous (fun y : Plane => η ‖y‖) := by
    rw [heq]
    exact (coreResolventSource_isTestFunction hr hφ).1.continuous
  have hs : Function.support (fun y : Plane => η ‖y‖) ⊆ Metric.closedBall (0 : Plane) p.r₀ := by
    rw [heq]
    exact coreResolventSource_support_subset_closedBall p φ
  have hi := integrableOn_radialFreeLandauAverage_mul hb hh hE hr hR hη hs
  have hij : Integrable (fun s : ℝ =>
      ((s : ℂ) * radialFreeLandauAverage b h E R s * η s).re / landauKernel b h E R)
      (volume.restrict (Ioi 0)) := hi.re.div_const (landauKernel b h E R)
  apply hij.congr
  filter_upwards [] with s
  simp only [η, regularLandauProfile, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ring

/-- The coefficient belongs to the given state, not a new choice of radial
ground state. An exterior identity at this single radius is sufficient. -/
theorem IsAtomicGroundState.radialCore_normalization
    {b coupling E R Γ : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) (hpos : IsPositiveRadial φ)
    (hb : 0 < b) (hc : 0 < coupling) (hr : 0 < p.r₀) (hR : p.r₀ < R)
    (hE : E = -(coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)
    (hEpos : 0 < E) (hKernel : FreeLandauResolventKernel b coupling E)
    (hΓ : φ (R • coordinateVector 0) = (Γ * landauKernel b coupling⁻¹ E R : ℂ)) :
    Γ = 2 * Real.pi * ∫ s in Ioi (0 : ℝ),
      s * regularLandauProfile b coupling⁻¹ E R s *
        (-p.coreRadialProfile s) * realRadialProfile φ s := by
  let η : ℝ → ℂ := fun s => ((-p.coreRadialProfile s * realRadialProfile φ s : ℝ) : ℂ)
  let G : ℝ → ℂ := fun s => (s : ℂ) * radialFreeLandauAverage b coupling⁻¹ E R s * η s
  have heq : (fun y : Plane => η ‖y‖) = coreResolventSource p φ := coreRadialSource_eq hpos
  have hη : Continuous (fun y : Plane => η ‖y‖) := by
    rw [heq]
    exact (coreResolventSource_isTestFunction hr hφ.1.1).1.continuous
  have hs : Function.support (fun y : Plane => η ‖y‖) ⊆ Metric.closedBall (0 : Plane) p.r₀ := by
    rw [heq]
    exact coreResolventSource_support_subset_closedBall p φ
  have hi : IntegrableOn G (Ioi 0) :=
    integrableOn_radialFreeLandauAverage_mul hb (inv_pos.mpr hc) hEpos hr hR hη hs
  have hx : p.r₀ < ‖R • coordinateVector 0‖ := by
    rwa [norm_radial_axis (hr.trans hR).le]
  have hrepr := hφ.radialCore_source_representation hr hb hc hE hEpos hKernel hx
  have hpolar := integral_freeLandauKernel_radial_eq_average hb (inv_pos.mpr hc) hEpos hr hR hη hs
  have hcomplex : (Γ * landauKernel b coupling⁻¹ E R : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ), G s := by
    rw [← hΓ, hrepr, ← hpolar]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [show η ‖y‖ = coreResolventSource p φ y from congrFun heq y]
      rfl
  have hre : Γ * landauKernel b coupling⁻¹ E R =
      2 * Real.pi * ∫ s in Ioi (0 : ℝ), (G s).re := by
    have hh := congrArg Complex.re hcomplex
    simp only [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hh
    have hint : (∫ s in Ioi (0 : ℝ), G s).re = ∫ s in Ioi (0 : ℝ), (G s).re :=
      (integral_re hi).symm
    rwa [hint] at hh
  have hnorm : (∫ s in Ioi (0 : ℝ), s * regularLandauProfile b coupling⁻¹ E R s *
      (-p.coreRadialProfile s) * realRadialProfile φ s) =
      (∫ s in Ioi (0 : ℝ), (G s).re) / landauKernel b coupling⁻¹ E R := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => by
      simp only [G, η, regularLandauProfile, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      ring
  rw [hnorm, ← mul_div_assoc]
  have hk : landauKernel b coupling⁻¹ E R ≠ 0 :=
    (landauKernel_pos hb (inv_pos.mpr hc) hEpos (hr.trans hR)).ne'
  exact (eq_div_iff hk).mpr hre

end InfiniteZero
