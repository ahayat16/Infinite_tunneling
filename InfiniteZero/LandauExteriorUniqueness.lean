import InfiniteZero.RadialExteriorEnergy
import InfiniteZero.LandauRadialEquation

/-! Uniqueness of the exterior radial L² branch for the actual Landau kernel.
The derivative energies are deduced by Caccioppoli, not supplied as inputs. -/

noncomputable section
open Set MeasureTheory
namespace InfiniteZero

def radialLandauCoefficient (b h E r : ℝ) : ℝ := (b ^ 2 * r ^ 2 / 4 + E) / h ^ 2

theorem isRadialODESolutionOn_landauKernel {b h E a : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (ha : 0 < a) :
    IsRadialODESolutionOn (radialLandauCoefficient b h E)
      (landauKernel b h E) (deriv (landauKernel b h E)) a := by
  constructor
  · intro r hr
    exact (hasDerivAt_landauKernel hb hh hE (ha.trans hr)).differentiableAt.hasDerivAt
  · intro r hr
    have hd := (hasDerivAt_deriv_landauKernel hb hh hE (ha.trans hr)).differentiableAt.hasDerivAt
    have heq : deriv (deriv (landauKernel b h E)) r =
        radialLandauCoefficient b h E r * landauKernel b h E r -
          r⁻¹ * deriv (landauKernel b h E) r := by
      have hode := landauKernel_radial_ode hb hh hE (ha.trans hr)
      calc
        _ = ((b ^ 2 * r ^ 2 / 4 + E) * landauKernel b h E r -
            h ^ 2 * (r⁻¹ * deriv (landauKernel b h E) r)) / h ^ 2 := by
          apply (eq_div_iff (pow_ne_zero 2 hh.ne')).mpr
          nlinarith only [hode]
        _ = _ := by unfold radialLandauCoefficient; field_simp
    rwa [heq] at hd

/-- Every real radial L² solution on an exterior interval is proportional to
the actual integral-defined kernel. No derivative decay or finite derivative
energy is assumed. -/
theorem exists_eq_mul_landauKernel_of_radialODE {b h E a : ℝ} {f df : ℝ → ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (ha : 0 < a)
    (hf : IsRadialODESolutionOn (radialLandauCoefficient b h E) f df a)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi a)) :
    ∃ Γ : ℝ, ∀ r ∈ Ioi a, f r = Γ * landauKernel b h E r := by
  have hk := isRadialODESolutionOn_landauKernel hb hh hE ha
  have hki : IntegrableOn (fun r => r * landauKernel b h E r ^ 2) (Ioi a) := by
    simpa only [Real.norm_eq_abs, sq_abs] using integrableOn_radial_landauKernel_sq hb hh hE ha
  have hq : ContinuousOn (radialLandauCoefficient b h E) (Ioi a) := by
    unfold radialLandauCoefficient
    fun_prop
  have hq0 : ∀ r ∈ Ioi a, 0 ≤ radialLandauCoefficient b h E r := by
    intro r _
    unfold radialLandauCoefficient
    positivity
  have hdfi := hf.integrableOn_radial_deriv_sq ha hq hq0 hfi
  have hdki := hk.integrableOn_radial_deriv_sq ha hq hq0 hki
  have hR : a ≤ a + 2 := by linarith
  exact exists_eq_mul_of_radialODE_of_integrable_tail ha hf hk hR
    (hfi.mono_set (Ioi_subset_Ioi hR)) hdfi (hki.mono_set (Ioi_subset_Ioi hR)) hdki
    (fun r hr => landauKernel_pos hb hh hE (ha.trans hr))

/-- A positive radial exterior solution has a strictly positive coefficient.
No estimate on that coefficient or its dependence on h is asserted here. -/
theorem exists_pos_eq_mul_landauKernel_of_radialODE {b h E a : ℝ} {f df : ℝ → ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (ha : 0 < a)
    (hf : IsRadialODESolutionOn (radialLandauCoefficient b h E) f df a)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi a))
    (hfpos : ∀ r ∈ Ioi a, 0 < f r) :
    ∃ Γ > 0, ∀ r ∈ Ioi a, f r = Γ * landauKernel b h E r := by
  obtain ⟨Γ, hΓ⟩ := exists_eq_mul_landauKernel_of_radialODE hb hh hE ha hf hfi
  refine ⟨Γ, ?_, hΓ⟩
  have hpos := hfpos (a + 1) (lt_add_one a)
  rw [hΓ (a + 1) (lt_add_one a)] at hpos
  exact (mul_pos_iff_of_pos_right (landauKernel_pos hb hh hE (by linarith))).mp hpos

end InfiniteZero
