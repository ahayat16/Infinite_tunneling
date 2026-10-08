import InfiniteZero.LandauKernelUniform

/-!
# An exact-action upper bound for the radial Landau kernel

Choosing the splitting parameter equal to `h` absorbs the auxiliary integral
at a fixed scale. This keeps the full action in the exponential and costs
only `h⁻²`, uniformly on positive energy-radius rectangles.
-/

noncomputable section
open Set

namespace InfiniteZero

theorem landauKernel_le_exact_action {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) (hh1 : h ≤ 1) :
    landauKernel b h E r ≤
      (Real.exp (bridgeAction b E r) / (Real.pi * E * r ^ 2)) *
        (h ^ 2)⁻¹ * Real.exp (-bridgeAction b E r / h) := by
  apply (landauKernel_le_exp_action hb hh hE hr hh hh1).trans_eq
  have he : -((1 - h) * bridgeAction b E r) / h =
      bridgeAction b E r + (-bridgeAction b E r / h) := by
    field_simp
    ring
  rw [he, Real.exp_add]
  field_simp

/-- The constant is fixed before the energy, radius and semiclassical
parameter. No loss is made in the action in the exponential. -/
theorem exists_uniform_landauKernel_exact_action_upper {b Emin Emax rmin rmax : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (_hEmax : Emin ≤ Emax)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) :
    ∃ C > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rmin rmax, ∀ h > 0, h ≤ 1 →
      landauKernel b h E r ≤ C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction b E r / h) := by
  have hrm : 0 < rmax := hrmin.trans_le hrmax
  refine ⟨Real.exp (bridgeAction b Emax rmax) / (Real.pi * Emin * rmin ^ 2),
    by positivity, ?_⟩
  intro E hE r hr h hh hh1
  have hEp : 0 < E := hEmin.trans_le hE.1
  have hrp : 0 < r := hrmin.trans_le hr.1
  have hJ : bridgeAction b E r ≤ bridgeAction b Emax rmax :=
    ((strictMono_bridgeAction hb.ne' hEp).monotone hr.2).trans
      (bridgeAction_energy_le hb.ne' hrm hEp hE.2)
  have hcoef : Real.exp (bridgeAction b E r) / (Real.pi * E * r ^ 2) ≤
      Real.exp (bridgeAction b Emax rmax) / (Real.pi * Emin * rmin ^ 2) := by
    apply div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hJ) (by positivity)
    gcongr
    · exact hE.1
    · exact hr.1
  exact (landauKernel_le_exact_action hb hh hEp hrp hh1).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr (sq_nonneg h)))
      (Real.exp_pos _).le)

end InfiniteZero
