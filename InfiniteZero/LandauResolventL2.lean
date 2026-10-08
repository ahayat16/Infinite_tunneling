import InfiniteZero.IntegralKernelSchur
import InfiniteZero.LandauHeatSpacetime
import InfiniteZero.LandauExteriorConvolution

/-!
# L² boundedness of the explicit standard Landau resolvent integral

The Laplace-transform bounds give absolute row and column masses at most
`1/ρ`. Schur's estimate therefore bounds the integral operator on test
sources by `1/ρ`, with no spectral or resolvent-identification assumption.
-/
noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem norm_freeLandauKernel_standard_swap (B ρ : ℝ) (x y : Plane) :
    ‖freeLandauKernel B 1 ρ x y‖ = ‖freeLandauKernel B 1 ρ y x‖ := by
  simp [freeLandauKernel, Complex.norm_exp, norm_sub_rev]

theorem integrable_freeLandauKernel_standard_left {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (y : Plane) :
    Integrable (fun x => freeLandauKernel B 1 ρ x y) := by
  have hm := (measurable_freeLandauKernel B 1 ρ).comp
    (measurable_prodMk_right (α := Plane) (y := y))
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  change Integrable (fun x : Plane => ‖freeLandauKernel B 1 ρ x y‖)
  simp_rw [norm_freeLandauKernel_standard_swap B ρ _ y]
  exact (integrable_freeLandauKernel_standard hB hρ y).norm

theorem integral_norm_freeLandauKernel_standard_left_le {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (y : Plane) :
    (∫ x : Plane, ‖freeLandauKernel B 1 ρ x y‖) ≤ 1 / ρ := by
  simp_rw [norm_freeLandauKernel_standard_swap B ρ _ y]
  exact integral_norm_freeLandauKernel_standard_le hB hρ y

/-- The explicit resolvent integral maps test functions into `L²`, with
squared norm bounded by `ρ⁻²` times the source mass. -/
theorem standardLandauResolventAction_memLp_mass_le {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) {f : Wavefunction} (hf : IsTestFunction f) :
    MemLp (standardLandauResolventAction B ρ f) 2 volume ∧
      mass (standardLandauResolventAction B ρ f) ≤ ρ⁻¹ ^ 2 * mass f := by
  simpa only [one_div, standardLandauResolventAction] using
    integralKernel_memLp_mass_bound (one_div_pos.mpr hρ)
      (measurable_freeLandauKernel B 1 ρ)
      (integrable_freeLandauKernel_standard hB hρ)
      (integrable_freeLandauKernel_standard_left hB hρ)
      (integral_norm_freeLandauKernel_standard_le hB hρ)
      (integral_norm_freeLandauKernel_standard_left_le hB hρ) hf

end InfiniteZero
