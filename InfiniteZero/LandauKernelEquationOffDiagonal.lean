import InfiniteZero.HoppingSourceIdentity
import InfiniteZero.MagneticCovariance
import InfiniteZero.MagneticRadialReduction
import InfiniteZero.LandauRadialEquation

/-!
# The free Landau kernel solves the source-variable equation off the diagonal

Magnetic covariance is proved locally at a point of class C². This avoids
any regularity assertion for the radial Green function at its singularity.
-/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace InfiniteZero

private def localMagneticPhaseLinear (b coupling : ℝ) (a : Plane) : Plane →L[ℝ] ℂ :=
  (-Complex.I) • (Complex.ofRealCLM.comp
    ((b * coupling / 2) •
      (a 1 • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 -
       a 0 • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)))

private theorem localMagneticPhaseLinear_apply (b coupling : ℝ) (a x : Plane) :
    localMagneticPhaseLinear b coupling a x =
      -Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ) := by
  simp only [localMagneticPhaseLinear, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, PiLp.proj_apply,
    smul_eq_mul, Complex.ofRealCLM_apply, wedge]
  congr 2
  ring

private theorem localMagneticPhaseLinear_coordinate (b coupling : ℝ) (a : Plane)
    (i : Fin 2) :
    localMagneticPhaseLinear b coupling a (coordinateVector i) =
      Complex.I * ((b * coupling / 2 * perpCoordinate a i : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [localMagneticPhaseLinear_apply, coordinateVector, wedge, perpCoordinate,
      Complex.ofReal_mul, Complex.ofReal_neg]

theorem partialDerivative_magneticTranslation_at (b coupling : ℝ) (a x : Plane)
    (i : Fin 2) {φ : Wavefunction} (hφ : DifferentiableAt ℝ φ (x - a)) :
    partialDerivative i (magneticTranslation b coupling a φ) x =
      Complex.exp (-Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ)) *
        (partialDerivative i φ (x - a) +
          Complex.I * ((b * coupling / 2 * perpCoordinate a i : ℝ) : ℂ) * φ (x - a)) := by
  have hd := ((localMagneticPhaseLinear b coupling a).hasFDerivAt.cexp).mul
    (hφ.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a))
  have he := congrArg (fun f : Plane →L[ℝ] ℂ => f (coordinateVector i)) hd.fderiv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    localMagneticPhaseLinear_coordinate, Function.comp_apply, id_eq] at he
  simp only [localMagneticPhaseLinear_apply] at he
  rw [show partialDerivative i (magneticTranslation b coupling a φ) x = _ from he]
  simp only [partialDerivative]
  ring

theorem covariantDerivative_magneticTranslation_at (b coupling : ℝ) (a x : Plane)
    (i : Fin 2) {φ : Wavefunction} (hφ : DifferentiableAt ℝ φ (x - a)) :
    covariantDerivative b coupling i (magneticTranslation b coupling a φ) x =
      magneticTranslation b coupling a (covariantDerivative b coupling i φ) x := by
  have hp : perpCoordinate (x - a) i = perpCoordinate x i - perpCoordinate a i := by
    unfold perpCoordinate
    split_ifs <;> simp only [PiLp.sub_apply]
    ring
  simp only [covariantDerivative, partialDerivative_magneticTranslation_at b coupling a x i hφ,
    magneticTranslation, hp, Complex.ofReal_mul, Complex.ofReal_sub]
  ring_nf
  simp [Complex.I_sq]

theorem covariantDerivative_congr_of_eventuallyEq (b coupling : ℝ) (i : Fin 2)
    {φ ψ : Wavefunction} {x : Plane} (heq : φ =ᶠ[𝓝 x] ψ) :
    covariantDerivative b coupling i φ x = covariantDerivative b coupling i ψ x := by
  simp only [covariantDerivative, partialDerivative, heq.fderiv_eq, heq.self_of_nhds]

/-- Local covariance requires only C² at the translated evaluation point. -/
theorem magneticHamiltonian_magneticTranslation_at (b coupling : ℝ) (a x : Plane)
    (V : Potential) {φ : Wavefunction} (hφ : ContDiffAt ℝ 2 φ (x - a)) :
    magneticHamiltonian b coupling (fun y => V (y - a))
        (magneticTranslation b coupling a φ) x =
      magneticTranslation b coupling a (magneticHamiltonian b coupling V φ) x := by
  have hcov (i : Fin 2) : DifferentiableAt ℝ (covariantDerivative b coupling i φ) (x - a) := by
    have hp : ContDiffAt ℝ 1 (partialDerivative i φ) (x - a) :=
      (hφ.fderiv_right (by norm_num)).clm_apply contDiffAt_const
    have hperp : ContDiffAt ℝ 1 (fun z : Plane => perpCoordinate z i) (x - a) :=
      (contDiff_perpCoordinate i).contDiffAt.of_le (by simp)
    exact ((contDiffAt_const.mul hp).sub
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _
        (contDiffAt_const.mul hperp)).mul
        (hφ.of_le (by norm_num)))).differentiableAt (by norm_num)
  have heq (i : Fin 2) :
      covariantDerivative b coupling i (magneticTranslation b coupling a φ) =ᶠ[𝓝 x]
        magneticTranslation b coupling a (covariantDerivative b coupling i φ) := by
    have ht : Tendsto (fun y : Plane => y - a) (𝓝 x) (𝓝 (x - a)) :=
      (continuous_id.sub continuous_const).continuousAt
    have hnear := ht.eventually (hφ.eventually (by norm_num))
    filter_upwards [hnear] with y hy
    exact covariantDerivative_magneticTranslation_at b coupling a y i
      (hy.differentiableAt (by norm_num))
  have hsecond (i : Fin 2) :
      covariantDerivative b coupling i
        (covariantDerivative b coupling i (magneticTranslation b coupling a φ)) x =
      magneticTranslation b coupling a
        (covariantDerivative b coupling i (covariantDerivative b coupling i φ)) x := by
    rw [covariantDerivative_congr_of_eventuallyEq b coupling i (heq i)]
    exact covariantDerivative_magneticTranslation_at b coupling a x i (hcov i)
  simp only [magneticHamiltonian, hsecond, magneticTranslation, ← Finset.mul_sum]
  ring

theorem contDiffAt_landauKernel {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    ContDiffAt ℝ ∞ (landauKernel b h E) r := by
  have hrC : (r : ℂ) ∈ complexLandauRadiusDomain := by
    simpa only [complexLandauRadiusDomain, mem_setOf_eq, ← Complex.ofReal_pow,
      Complex.ofReal_re] using sq_pos_of_pos hr
  have hc : ContDiffAt ℂ ∞ (complexLandauKernel b h E) (r : ℂ) :=
    ((analyticOnNhd_complexLandauKernel hb hh hE) _ hrC).contDiffAt
  have hreal := Complex.reCLM.contDiff.contDiffAt.comp r
    ((hc.restrict_scalars ℝ).comp r Complex.ofRealCLM.contDiff.contDiffAt)
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofRealCLM_apply,
    complexLandauKernel_ofReal, Complex.ofReal_re] using hreal

theorem contDiffAt_radial_landauKernel {b h E : ℝ} {x : Plane}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Plane => (landauKernel b h E ‖y‖ : ℂ)) x :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((contDiffAt_landauKernel hb hh hE (norm_pos_iff.mpr hx)).comp x
      (contDiffAt_norm ℝ hx))

theorem freeLandauKernel_eq_magneticTranslation (b coupling E : ℝ) (x : Plane) :
    freeLandauKernel b coupling⁻¹ E x =
      magneticTranslation (-b) coupling x
        (fun z => (landauKernel b coupling⁻¹ E ‖z‖ : ℂ)) := by
  funext y
  have hw : wedge y x = -wedge x y := by unfold wedge; ring
  have hc : (-b) * coupling / 2 * wedge y x = b / (2 * coupling⁻¹) * wedge x y := by
    rw [hw]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  unfold freeLandauKernel magneticTranslation
  dsimp only
  rw [hc, norm_sub_rev y x]
  exact mul_comm _ _

/-- The source variable carries the opposite magnetic field. -/
theorem freeLandauKernel_source_equation {b coupling E : ℝ} {x y : Plane}
    (hb : 0 < b) (hc : 0 < coupling) (hE : 0 < E) (hxy : x ≠ y) :
    magneticHamiltonian (-b) coupling 0 (freeLandauKernel b coupling⁻¹ E x) y +
      ((coupling ^ 2 * E : ℝ) : ℂ) * freeLandauKernel b coupling⁻¹ E x y = 0 := by
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hc
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hr : 0 < ‖y - x‖ := norm_pos_iff.mpr hyx
  have hK := contDiffAt_radial_landauKernel hb hh hE hyx
  have hrad := magneticHamiltonian_radial
    (fun r hr => (hasDerivAt_landauKernel hb hh hE hr).differentiableAt.hasDerivAt) hyx
    (hasDerivAt_deriv_landauKernel hb hh hE hr).differentiableAt.hasDerivAt (-b) coupling 0
  have hode := landauKernel_radial_ode hb hh hE hr
  have hreal :
      -deriv (deriv (landauKernel b coupling⁻¹ E)) ‖y - x‖ -
        ‖y - x‖⁻¹ * deriv (landauKernel b coupling⁻¹ E) ‖y - x‖ +
        ((-b) ^ 2 * coupling ^ 2 / 4 * ‖y - x‖ ^ 2 + coupling ^ 2 * (0 : Potential) (y - x)) *
          landauKernel b coupling⁻¹ E ‖y - x‖ +
        coupling ^ 2 * E * landauKernel b coupling⁻¹ E ‖y - x‖ = 0 := by
    have hm := congrArg (fun t : ℝ => coupling ^ 2 * t) hode
    convert hm using 1
    · simp only [mul_zero, Pi.zero_apply, neg_sq]
      field_simp [hc.ne', hr.ne']
      ring
    · simp
  rw [freeLandauKernel_eq_magneticTranslation]
  rw [show (0 : Potential) = (fun z => (0 : Potential) (z - x)) from rfl,
    magneticHamiltonian_magneticTranslation_at (-b) coupling x y 0
      (hK.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
  simp only [magneticTranslation, hrad]
  convert congrArg (fun t : ℝ =>
    Complex.exp (-Complex.I * (((-b) * coupling / 2 * wedge y x : ℝ) : ℂ)) * (t : ℂ))
    hreal using 1 <;> push_cast <;> ring

end InfiniteZero
