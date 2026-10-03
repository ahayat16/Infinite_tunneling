import InfiniteZero.MagneticDilation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A uniform coupling bound for the globally dilated potential

For `W_c(y) = c V(c⁻¹ᐟ² y)`, differentiation in `c > 0` gives
`V(z) - DV(z)[z] / 2`, with `z = c⁻¹ᐟ² y`. This generator is continuous
and compactly supported when `V` is smooth and compactly supported.
Its single global bound controls all positive couplings and all spatial
points by the mean value theorem.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

/-- The potential appearing after the global magnetic dilation. -/
def magneticDilationPotential (V : Potential) (coupling : ℝ) : Potential :=
  fun y => coupling * V ((Real.sqrt coupling)⁻¹ • y)

/-- Exact derivative in the positive coupling parameter. -/
theorem hasDerivAt_magneticDilationPotential {V : Potential}
    (hV : Differentiable ℝ V) {coupling : ℝ} (hc : 0 < coupling) (y : Plane) :
    HasDerivAt (fun c : ℝ => magneticDilationPotential V c y)
      (V ((Real.sqrt coupling)⁻¹ • y) -
        (1 / 2 : ℝ) * fderiv ℝ V ((Real.sqrt coupling)⁻¹ • y)
          ((Real.sqrt coupling)⁻¹ • y)) coupling := by
  have hs : Real.sqrt coupling ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hi : HasDerivAt (fun c : ℝ => (Real.sqrt c)⁻¹)
      (-((Real.sqrt coupling)⁻¹) / (2 * coupling)) coupling := by
    convert (Real.hasDerivAt_sqrt hc.ne').inv hs using 1
    field_simp
    nlinarith [Real.sq_sqrt hc.le]
  have hv := (hV ((Real.sqrt coupling)⁻¹ • y)).hasFDerivAt.comp_hasDerivAt
    coupling (hi.smul_const y)
  convert (hasDerivAt_id coupling).mul hv using 1
  simp only [id_eq, one_mul, Function.comp_apply, ContinuousLinearMap.map_smul, smul_eq_mul]
  field_simp
  ring

theorem continuousOn_magneticDilationPotential {V : Potential}
    (hV : Differentiable ℝ V) (y : Plane) :
    ContinuousOn (fun c : ℝ => magneticDilationPotential V c y) (Ioi 0) :=
  fun _ hc => (hasDerivAt_magneticDilationPotential hV hc y).continuousAt.continuousWithinAt

/-- Compactness bounds the dilation generator before any coupling or point is chosen. -/
theorem exists_magneticDilationPotential_generator_bound {V : Potential}
    (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V) :
    ∃ C > 0, ∀ z : Plane, |V z - (1 / 2 : ℝ) * fderiv ℝ V z z| ≤ C := by
  have hc : Continuous (fun z : Plane => V z - (1 / 2 : ℝ) * fderiv ℝ V z z) :=
    hV.continuous.sub (continuous_const.mul
      ((hV.continuous_fderiv (by simp)).clm_apply continuous_id))
  have hd : HasCompactSupport (fun z : Plane => fderiv ℝ V z z) := by
    apply (hcompact.fderiv ℝ).mono
    intro z hz
    change fderiv ℝ V z ≠ 0
    intro heq
    apply hz
    change fderiv ℝ V z z = 0
    rw [heq]
    rfl
  have hg : HasCompactSupport (fun z : Plane => V z - (1 / 2 : ℝ) * fderiv ℝ V z z) :=
    hcompact.sub hd.mul_left
  obtain ⟨C, hC, hbound⟩ := (hg.isCompact_range hc).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun z => hbound _ ⟨z, rfl⟩⟩

/-- One Lipschitz constant works on the whole positive coupling half-line, uniformly in space. -/
theorem exists_magneticDilationPotential_lipschitz {V : Potential}
    (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V) :
    ∃ C > 0, ∀ c μ : ℝ, 0 < c → 0 < μ → ∀ y : Plane,
      |magneticDilationPotential V c y - magneticDilationPotential V μ y| ≤
        C * |c - μ| := by
  obtain ⟨C, hC, hbound⟩ := exists_magneticDilationPotential_generator_bound hV hcompact
  refine ⟨C, hC, ?_⟩
  intro c μ hc hμ y
  exact (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun ν hν => (hasDerivAt_magneticDilationPotential
      (hV.differentiable (by simp)) hν y).hasDerivWithinAt)
    (fun ν _ => hbound ((Real.sqrt ν)⁻¹ • y)) hμ hc

end InfiniteZero
