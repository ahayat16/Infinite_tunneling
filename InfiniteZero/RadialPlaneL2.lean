import InfiniteZero.CuspChartJacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.L2Space

/-!
# From physical planar L² to radial integrability

Cartesian coordinates preserve the physical volume on `Plane`. The genuine
polar change of variables has Jacobian `r`, and its angular interval has
positive measure. Thus a radial integrable function on the plane gives an
integrable radial density. Applied to the square of a real profile, this
transfers planar L² to exterior radial L². No continuity hypothesis on the
profile is needed.
-/

noncomputable section
open Set MeasureTheory
open InfiniteZero.CuspParameters
open scoped ENNReal

namespace InfiniteZero

/-- Euclidean radius in the actual Cartesian realization of polar coordinates. -/
theorem norm_planeCartesianEquiv_symm_polarCoord (q : ℝ × ℝ) :
    ‖planeCartesianEquiv.symm (polarCoord.symm q)‖ = |q.1| := by
  have hs : ‖planeCartesianEquiv.symm (polarCoord.symm q)‖ ^ 2 = q.1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [planeCartesianEquiv_symm_apply, polarCoord_symm_apply,
      Fin.sum_univ_two, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (planeCartesianEquiv.symm (polarCoord.symm q)), abs_nonneg q.1,
    sq_abs q.1]

/-- Integrability after the actual polar Jacobian, before integrating out angles. -/
theorem integrableOn_polar_radialDensity {F : ℝ → ℝ}
    (hF : Integrable (fun x : Plane => F ‖x‖) volume) :
    IntegrableOn (fun q : ℝ × ℝ => q.1 * F q.1) polarCoord.target volume := by
  have hcart := planeCartesianEquiv_symm_measurePreserving.integrable_comp_of_integrable hF
  have hpolar := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun q _ => (hasFDerivAt_polarCoord_symm q).hasFDerivWithinAt)
    polarCoord.symm.injOn (fun q => F ‖planeCartesianEquiv.symm q‖)).mp hcart.integrableOn
  apply hpolar.congr_fun _ polarCoord.open_target.measurableSet
  intro q hq
  have hr : (0 : ℝ) < q.1 := hq.1
  simp only [det_fderivPolarCoordSymm, smul_eq_mul,
    norm_planeCartesianEquiv_symm_polarCoord, abs_of_pos hr]

/-- Removing the nonzero angular factor yields integrability with radial measure. -/
theorem integrableOn_radialDensity_of_integrable_plane {F : ℝ → ℝ}
    (hF : Integrable (fun x : Plane => F ‖x‖) volume) :
    IntegrableOn (fun r : ℝ => r * F r) (Ioi 0) volume := by
  have hp := integrableOn_polar_radialDensity hF
  change Integrable (fun q : ℝ × ℝ => q.1 * F q.1)
    ((volume : Measure (ℝ × ℝ)).restrict ((Ioi 0) ×ˢ Ioo (-Real.pi) Real.pi)) at hp
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  apply hp.of_comp_fst
  intro hz
  have hm := Measure.restrict_eq_zero.mp hz
  rw [Real.volume_Ioo] at hm
  have hn : ENNReal.ofReal (Real.pi - -Real.pi) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by linarith [Real.pi_pos])
  exact hn hm

/-- Planar L² of a real radial profile gives its full radial L² density. -/
theorem integrableOn_radial_sq_of_memLp {f : ℝ → ℝ}
    (hψ : MemLp (fun x : Plane => (f ‖x‖ : ℂ)) 2 volume) :
    IntegrableOn (fun r : ℝ => r * f r ^ 2) (Ioi 0) volume := by
  apply integrableOn_radialDensity_of_integrable_plane
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hψ.norm.integrable_sq

/-- Exterior version, with no smoothness or radial differential equation assumed. -/
theorem integrableOn_exterior_radial_sq_of_memLp {f : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hψ : MemLp (fun x : Plane => (f ‖x‖ : ℂ)) 2 volume) :
    IntegrableOn (fun r : ℝ => r * f r ^ 2) (Ioi a) volume :=
  (integrableOn_radial_sq_of_memLp hψ).mono_set (Ioi_subset_Ioi ha.le)

/-- The interface for a physical wavefunction identified with a real radial profile. -/
theorem integrableOn_exterior_radial_sq_of_representation
    {ψ : Wavefunction} {f : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hψ : MemLp ψ 2 volume)
    (hradial : ∀ x, ψ x = (f ‖x‖ : ℂ)) :
    IntegrableOn (fun r : ℝ => r * f r ^ 2) (Ioi a) volume := by
  apply integrableOn_exterior_radial_sq_of_memLp ha
  exact (memLp_congr_ae (Filter.Eventually.of_forall hradial)).mp hψ

end InfiniteZero
