import InfiniteZero.AtomicLocalizationCutoffs
import InfiniteZero.ConstructionSmooth
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Energy inequalities for the actual atomic localization

These pointwise estimates use the concrete core, cusp potential, and fixed
IMS cutoffs. They are independent of any spectral existence assertion.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

theorem magneticKinetic_nonneg (b coupling : ℝ) (ψ : Wavefunction) (x : Plane) :
    0 ≤ ∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

namespace CuspParameters

/-- The localized inner form sees exactly the radial reference potential. -/
theorem atomicInnerCutoff_energyDensity_eq_core {p : CuspParameters}
    (hp : p.BasicConditions) (coupling : ℝ) (ψ : Wavefunction) (x : Plane) :
    magneticEnergyDensity p.b coupling p.potential
      (fun y => (atomicInnerCutoff p hp.r₀_pos y : ℂ) * ψ y) x =
    magneticEnergyDensity p.b coupling p.core
      (fun y => (atomicInnerCutoff p hp.r₀_pos y : ℂ) * ψ y) x := by
  have he := potential_mul_atomicInnerCutoff hp x
  simp only [magneticEnergyDensity, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  congr 1
  linear_combination coupling ^ 2 * atomicInnerCutoff p hp.r₀_pos x * ‖ψ x‖ ^ 2 * he

/-- Fixed exterior reserve for the actual potential at scaled energies ≤ -3/4. -/
theorem atomicOuterCutoff_energyDensity_lower {p : CuspParameters}
    (hp : p.BasicConditions) {e : ℝ} (he : e ≤ -(3 / 4 : ℝ))
    (coupling : ℝ) (ψ : Wavefunction) (x : Plane) :
    coupling ^ 2 / 4 * ‖(atomicOuterCutoff p hp.r₀_pos x : ℂ) * ψ x‖ ^ 2 ≤
      magneticEnergyDensity p.b coupling p.potential
        (fun y => (atomicOuterCutoff p hp.r₀_pos y : ℂ) * ψ y) x -
      coupling ^ 2 * e * ‖(atomicOuterCutoff p hp.r₀_pos x : ℂ) * ψ x‖ ^ 2 := by
  have hv := mul_le_mul_of_nonneg_left (atomicOuterCutoff_potential_lower hp he x)
    (mul_nonneg (sq_nonneg coupling) (sq_nonneg ‖ψ x‖))
  have hk := magneticKinetic_nonneg p.b coupling
    (fun y => (atomicOuterCutoff p hp.r₀_pos y : ℂ) * ψ y) x
  simp only [magneticEnergyDensity, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  nlinarith

/-- Kinetic positivity and the exact depth -1 control mass outside the core. -/
theorem core_exteriorMass_density_le (p : CuspParameters) (b coupling : ℝ)
    (ψ : Wavefunction) (x : Plane) :
    coupling ^ 2 * ({x : Plane | p.r₀ ≤ ‖x‖}.indicator (fun x => ‖ψ x‖ ^ 2) x) ≤
      magneticEnergyDensity b coupling p.core ψ x + coupling ^ 2 * ‖ψ x‖ ^ 2 := by
  classical
  have hk := magneticKinetic_nonneg b coupling ψ x
  by_cases hx : p.r₀ ≤ ‖x‖
  · have hc : p.core x = 0 := by simp [core, not_lt.mpr hx]
    rw [indicator_of_mem (show x ∈ {x : Plane | p.r₀ ≤ ‖x‖} from hx)]
    simp only [magneticEnergyDensity, hc, mul_zero, zero_mul, add_zero]
    linarith
  · have hv := (core_range p x).1
    have hm := mul_nonneg (sq_nonneg coupling) (sq_nonneg ‖ψ x‖)
    have hmul := mul_nonneg (show 0 ≤ p.core x + 1 by linarith) hm
    rw [indicator_of_notMem (show x ∉ {x : Plane | p.r₀ ≤ ‖x‖} from hx)]
    simp only [mul_zero, magneticEnergyDensity]
    nlinarith

/-- Exterior mass from the actual core form. This also applies to noncompact
states once integrability of their energy density has been established. -/
theorem core_exteriorMass_le {p : CuspParameters} {b coupling : ℝ}
    {ψ : Wavefunction} (hψ : MemLp ψ 2 volume)
    (hform : Integrable (magneticEnergyDensity b coupling p.core ψ)) :
    coupling ^ 2 * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖ψ x‖ ^ 2) ≤
      magneticForm b coupling p.core ψ + coupling ^ 2 * mass ψ := by
  classical
  have hS : MeasurableSet {x : Plane | p.r₀ ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hmass := hψ.norm.integrable_sq
  have hi := integral_mono ((hmass.indicator hS).const_mul (coupling ^ 2))
    (hform.add (hmass.const_mul (coupling ^ 2)))
    (core_exteriorMass_density_le p b coupling ψ)
  simpa only [Pi.add_apply, integral_const_mul, integral_indicator hS,
    integral_add hform (hmass.const_mul (coupling ^ 2)),
    magneticForm_eq_integral_density, mass] using hi

/-- An O(coupling) excess above the well depth forces O(1/coupling)
exterior probability. No Agmon estimate is used. -/
theorem core_exteriorMass_le_of_energy_upper {p : CuspParameters} {b coupling B : ℝ}
    {ψ : Wavefunction} (hCoupling : 0 < coupling) (hψ : MemLp ψ 2 volume)
    (hform : Integrable (magneticEnergyDensity b coupling p.core ψ))
    (hupper : magneticForm b coupling p.core ψ ≤
      (-coupling ^ 2 + B * coupling) * mass ψ) :
    (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖ψ x‖ ^ 2) ≤ B / coupling * mass ψ := by
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hCoupling)).mp
  have hm := core_exteriorMass_le hψ hform
  calc
    _ ≤ B * coupling * mass ψ := by nlinarith only [hm, hupper]
    _ = coupling ^ 2 * (B / coupling * mass ψ) := by field_simp

end CuspParameters
end InfiniteZero
