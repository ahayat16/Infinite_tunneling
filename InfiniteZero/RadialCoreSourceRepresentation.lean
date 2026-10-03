import InfiniteZero.LandauResolventBridge
import InfiniteZero.LandauExteriorConvolution

/-!
# The pointwise resolvent representation of a core ground state

The normalized source is `-core * φ`. Its regularity and compact support
follow from the explicit core and the differential eigenfunction definition.
The universal free resolvent contract initially gives an almost-everywhere
identity with source `-coupling² * core * φ`. The factors `coupling²` and
`coupling⁻²` cancel exactly, and exterior continuity gives equality at every
point outside the core ball. No radiality or positivity of the state is used.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff

namespace InfiniteZero

/-- The source in the semiclassical free resolvent equation for the core. -/
def coreResolventSource (p : CuspParameters) (φ : Wavefunction) : Wavefunction :=
  fun x => -(p.core x : ℂ) * φ x

theorem coreResolventSource_support_subset_closedBall
    (p : CuspParameters) (φ : Wavefunction) :
    Function.support (coreResolventSource p φ) ⊆ closedBall (0 : Plane) p.r₀ := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_contra hn
  have hc : p.core x = 0 := by
    simp [CuspParameters.core, not_lt.mpr (le_of_not_ge hn)]
  exact hx (by simp [coreResolventSource, hc])

theorem coreResolventSource_hasCompactSupport (p : CuspParameters) (φ : Wavefunction) :
    HasCompactSupport (coreResolventSource p φ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) p.r₀)
    (coreResolventSource_support_subset_closedBall p φ)

theorem coreResolventSource_isTestFunction {p : CuspParameters} {φ : Wavefunction}
    (hr : 0 < p.r₀) (hφ : ContDiff ℝ ∞ φ) :
    IsTestFunction (coreResolventSource p φ) := by
  refine ⟨?_, coreResolventSource_hasCompactSupport p φ⟩
  exact (Complex.ofRealCLM.contDiff.comp (CuspParameters.core_contDiff hr)).neg.mul hφ

theorem integrable_coreResolventSource {p : CuspParameters} {φ : Wavefunction}
    (hr : 0 < p.r₀) (hφ : ContDiff ℝ ∞ φ) :
    Integrable (coreResolventSource p φ) := by
  have hs := coreResolventSource_isTestFunction hr hφ
  exact hs.1.continuous.integrable_of_hasCompactSupport hs.2

/-- The unscaled differential equation has source `coupling²` times the
normalized source. This is a pointwise consequence of the actual eigen-equation. -/
theorem IsAtomicGroundState.radialCore_resolvent_equation
    {b coupling E : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) (hc : 0 < coupling)
    (hE : E = -(coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)
    (x : Plane) :
    magneticHamiltonian b coupling 0 φ x + ((coupling ^ 2 * E : ℝ) : ℂ) * φ x =
      ((coupling ^ 2 : ℝ) : ℂ) * coreResolventSource p φ x := by
  have hscale : coupling ^ 2 * E = -atomicGroundEnergy b p.core coupling := by
    rw [hE]
    field_simp
  rw [hscale, Complex.ofReal_neg]
  have he := hφ.1.2.2 x
  simp only [magneticHamiltonian, Pi.zero_apply, mul_zero, Complex.ofReal_zero,
    zero_mul, add_zero, coreResolventSource, Complex.ofReal_mul] at he ⊢
  linear_combination he

/-- Cancellation of the physical source scaling in the classical kernel
contract. This equality is initially only almost everywhere. -/
theorem IsAtomicGroundState.radialCore_source_representation_ae
    {b coupling E : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) (hr : 0 < p.r₀)
    (hc : 0 < coupling)
    (hE : E = -(coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)
    (hKernel : FreeLandauResolventKernel b coupling E) :
    ∀ᵐ x : Plane, φ x = ∫ y : Plane,
      freeLandauKernel b coupling⁻¹ E x y * (-(p.core y : ℂ) * φ y) := by
  have hs := coreResolventSource_isTestFunction hr hφ.1.1
  have hscaled : IsTestFunction
      (fun y => ((coupling ^ 2 : ℝ) : ℂ) * coreResolventSource p φ y) := by
    refine ⟨contDiff_const.mul hs.1, ?_⟩
    apply HasCompactSupport.intro hs.2
    intro y hy
    have hz := image_eq_zero_of_notMem_tsupport (f := coreResolventSource p φ) hy
    simp only [hz, mul_zero]
  have heq := hKernel φ _ hφ.1.1 hφ.1.2.1 hscaled
    (hφ.radialCore_resolvent_equation hc hE)
  have hcancel : (((coupling⁻¹) ^ 2 : ℝ) : ℂ) * ((coupling ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    field_simp
  filter_upwards [heq] with x hx
  have hi : (∫ y : Plane, freeLandauKernel b coupling⁻¹ E x y *
      (((coupling ^ 2 : ℝ) : ℂ) * coreResolventSource p φ y)) =
      ((coupling ^ 2 : ℝ) : ℂ) * ∫ y : Plane,
        freeLandauKernel b coupling⁻¹ E x y * coreResolventSource p φ y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [hi, ← mul_assoc, hcancel, one_mul] at hx
  exact hx

/-- The normalized source convolution is absolutely convergent outside the
core ball, with no assumptions on the phase or radiality of the state. -/
theorem integrable_radialCore_source_kernel
    {b coupling E : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hb : 0 < b) (hc : 0 < coupling) (hEpos : 0 < E) (hr : 0 < p.r₀)
    (hφ : ContDiff ℝ ∞ φ) {x : Plane} (hx : p.r₀ < ‖x‖) :
    Integrable (fun y : Plane =>
      freeLandauKernel b coupling⁻¹ E x y * (-(p.core y : ℂ) * φ y)) :=
  integrable_freeLandauKernel_mul_of_support_subset_closedBall hb (inv_pos.mpr hc) hEpos
    (coreResolventSource_isTestFunction hr hφ).1.continuous
    (coreResolventSource_support_subset_closedBall p φ) hx

/-- The classical almost-everywhere representation holds at every exterior
point, by continuity of the true eigenfunction and of the source convolution. -/
theorem IsAtomicGroundState.radialCore_source_representation
    {b coupling E : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) (hr : 0 < p.r₀)
    (hb : 0 < b) (hc : 0 < coupling)
    (hE : E = -(coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)
    (hEpos : 0 < E) (hKernel : FreeLandauResolventKernel b coupling E)
    {x : Plane} (hx : p.r₀ < ‖x‖) :
    φ x = ∫ y : Plane,
      freeLandauKernel b coupling⁻¹ E x y * (-(p.core y : ℂ) * φ y) := by
  exact eqOn_landauConvolution_exterior_of_ae_eq hb (inv_pos.mpr hc) hEpos
    (coreResolventSource_isTestFunction hr hφ.1.1).1.continuous
    (coreResolventSource_support_subset_closedBall p φ) hφ.1.1.continuous.continuousOn
    (hφ.radialCore_source_representation_ae hr hc hE hKernel) hx

end InfiniteZero
