import InfiniteZero.WavefunctionL2Bridge
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuous restriction of the physical L² space

The squared norm after restriction is the actual mass on the specified set.
No regularity of a chosen representative, or of its derivatives, is required.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

def l2Restrict (s : Set Plane) :
    L2Space →L[ℂ] Lp ℂ 2 (volume.restrict s) :=
  LpToLpRestrictCLM Plane ℂ ℂ volume 2 s

theorem norm_l2Restrict_sq {u : L2Space} {ψ : Wavefunction}
    (hu : Represents u ψ) (s : Set Plane) :
    ‖l2Restrict s u‖ ^ 2 = ∫ x in s, ‖ψ x‖ ^ 2 := by
  have hae : (l2Restrict s u : Plane → ℂ) =ᵐ[volume.restrict s] ψ :=
    (LpToLpRestrictCLM_coeFn ℂ s u).trans (ae_restrict_of_ae hu)
  calc
    ‖l2Restrict s u‖ ^ 2 = (inner ℂ (l2Restrict s u) (l2Restrict s u)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∫ x in s, ((‖ψ x‖ ^ 2 : ℝ) : ℂ)).re := by
      rw [L2.inner_def]
      apply congrArg Complex.re
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      simp only [hx, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
      rfl
    _ = ∫ x in s, ‖ψ x‖ ^ 2 := by
      rw [integral_complex_ofReal, Complex.ofReal_re]

theorem continuous_restricted_mass (s : Set Plane) :
    Continuous (fun u : L2Space => ‖l2Restrict s u‖ ^ 2) :=
  (l2Restrict s).continuous.norm.pow 2

end InfiniteZero
