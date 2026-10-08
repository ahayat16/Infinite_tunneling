import InfiniteZero.CoreQuadraticBound
import InfiniteZero.ConstructionCoreSmooth
import InfiniteZero.ConstructionCompact
import InfiniteZero.SecondEnergyTestSpace

/-!
# A variational upper bound for the radial core

A normalized compactly supported test, contracted at scale `coupling⁻¹ᐟ²`,
proves the upper bound `-coupling² + B * coupling`. The proof uses the
quadratic bound on the explicit potential and the exact magnetic dilation;
no spectral approximation or eigenfunction existence is required.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace InfiniteZero

private theorem magneticForm_le_of_potential_le (b coupling : ℝ)
    {V W : Potential} (hV : Continuous V) (hW : Continuous W)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) (hle : ∀ x, V x ≤ W x) :
    magneticForm b coupling V ψ ≤ magneticForm b coupling W ψ := by
  apply integral_mono (hψ.integrable_magneticEnergyDensity b coupling hV)
    (hψ.integrable_magneticEnergyDensity b coupling hW)
  intro x
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hle x) (sq_nonneg coupling)) (sq_nonneg ‖ψ x‖)) _

private theorem magneticForm_sub_constant (b coupling c : ℝ)
    {V : Potential} (hV : Continuous V) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    magneticForm b coupling (fun x => V x - c) ψ =
      magneticForm b coupling V ψ - coupling ^ 2 * c * mass ψ := by
  have h := magneticForm_sub_eq_potential_integral b coupling
    (V := fun x => V x - c) (hV.sub continuous_const) hV hψ
  have hint : (∫ x : Plane, (V x - c - V x) * ‖ψ x‖ ^ 2) = -c * mass ψ := by
    simp only [sub_sub_cancel_left, integral_const_mul, mass]
  rw [hint] at h
  linarith

namespace CuspParameters

/-- The complex-valued core itself provides a nonzero smooth compactly
supported test, which can be normalized by its positive `L²` mass. -/
theorem exists_normalized_core_test {p : CuspParameters} (hr : 0 < p.r₀) :
    ∃ ψ : Wavefunction, IsNormalizedTest ψ := by
  let φ : Wavefunction := fun x => (p.core x : ℂ)
  have hφ : IsTestFunction φ :=
    ⟨Complex.ofRealCLM.contDiff.comp (core_contDiff hr),
      (core_hasCompactSupport p).comp_left (g := Complex.ofReal) (by simp)⟩
  have hne : φ ≠ 0 := by
    intro hz
    have h := congrFun hz 0
    simp [φ, core_zero hr] at h
  have hm := hφ.mass_pos_of_ne_zero hne
  let r : ℝ := (Real.sqrt (mass φ))⁻¹
  have hr' : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  refine ⟨(r : ℂ) • φ, hφ.smul _, ?_⟩
  rw [mass_smul_wavefunction, Complex.norm_real, Real.norm_of_nonneg hr'.le]
  dsimp only [r]
  rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']

private theorem core_test_form_values_bddBelow (b coupling : ℝ)
    {p : CuspParameters} (hr : 0 < p.r₀) :
    BddBelow {E | ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧
      magneticForm b coupling p.core ψ = E} := by
  refine ⟨-coupling ^ 2, ?_⟩
  rintro E ⟨ψ, hψ, rfl⟩
  have h := abs_magneticForm_sub_le (W := 0) b coupling (core_contDiff hr).continuous
    continuous_const hψ.1 (δ := 1) (fun x => by
      simpa only [Pi.zero_apply, sub_zero] using abs_le.mpr
        ⟨(core_range p x).1, (core_range p x).2.trans (by norm_num)⟩)
  rw [hψ.2, mul_one, mul_one] at h
  have hfree := magneticForm_zero_potential_nonneg b coupling ψ
  have hlo := (abs_le.mp h).1
  linarith

/-- A quadratic upper bound near the minimum, valid globally, gives an
energy upper bound through a compactly supported variational trial state. -/
theorem exists_atomicGroundEnergy_upper_of_core_quadratic
    (b : ℝ) {p : CuspParameters} (hr : 0 < p.r₀)
    {K : ℝ} (hquad : ∀ x, p.core x + 1 ≤ K * ‖x‖ ^ 2) :
    ∃ B > 0, ∀ coupling : ℝ, 0 < coupling →
      atomicGroundEnergy b p.core coupling ≤ -coupling ^ 2 + B * coupling := by
  obtain ⟨ψ, hψ⟩ := exists_normalized_core_test hr
  let Q : Potential := fun x => K * ‖x‖ ^ 2
  have hQ : Continuous Q := continuous_const.mul (continuous_norm.pow 2)
  let C := magneticForm b 1 Q ψ
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro coupling hc
  let u := magneticDilation coupling⁻¹ ψ
  have hu : IsNormalizedTest u := hψ.magneticDilation (inv_pos.mpr hc)
  have hInf : atomicGroundEnergy b p.core coupling ≤ magneticForm b coupling p.core u :=
    csInf_le (core_test_form_values_bddBelow b coupling hr) ⟨u, hu, rfl⟩
  have hscale := magneticForm_magneticDilation b p.core hc hu.1
  have hcancel : magneticDilation coupling u = ψ := magneticDilation_cancel_inv hc ψ
  rw [hcancel] at hscale
  have hpotential (x : Plane) :
      coupling * p.core ((Real.sqrt coupling)⁻¹ • x) ≤ Q x - coupling := by
    have h := mul_le_mul_of_nonneg_left
      (hquad ((Real.sqrt coupling)⁻¹ • x)) hc.le
    have hs : coupling * ‖(Real.sqrt coupling)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hc.le]
      field_simp
    rw [mul_left_comm coupling K, hs] at h
    dsimp only [Q]
    linarith only [h]
  have hform := magneticForm_le_of_potential_le b 1
    (continuous_const.mul ((core_contDiff hr).continuous.comp
      (continuous_id.const_smul _))) (hQ.sub continuous_const) hψ.1 hpotential
  change magneticForm b 1 (fun x => coupling * p.core ((Real.sqrt coupling)⁻¹ • x)) ψ ≤
    magneticForm b 1 (fun x => Q x - coupling) ψ at hform
  rw [hscale, magneticForm_sub_constant b 1 coupling hQ hψ.1,
    one_pow, one_mul, hψ.2, mul_one] at hform
  have hmul := mul_le_mul_of_nonneg_left hform hc.le
  have hmul' : magneticForm b coupling p.core u ≤ coupling * (C - coupling) := by
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, C] using hmul
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have hupper := mul_le_mul_of_nonneg_right hC hc.le
  nlinarith [hInf, hmul']

/-- The explicit radial core satisfies the upper energy estimate at every
positive coupling, with a constant fixed independently of the coupling. -/
theorem exists_core_atomicGroundEnergy_upper (b : ℝ) {p : CuspParameters}
    (hr : 0 < p.r₀) :
    ∃ B > 0, ∀ coupling : ℝ, 0 < coupling →
      atomicGroundEnergy b p.core coupling ≤ -coupling ^ 2 + B * coupling :=
  exists_atomicGroundEnergy_upper_of_core_quadratic b hr (core_add_one_le_quadratic hr)

/-- The same variational estimate in the semiclassical normalization
used by `RadialCoreSpectralData`, with `h = coupling⁻¹`. -/
theorem exists_core_scaledAtomicGroundEnergy_upper (b : ℝ) {p : CuspParameters}
    (hr : 0 < p.r₀) :
    ∃ B > 0, ∀ coupling : ℝ, 0 < coupling →
      (coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling ≤ -1 + B / coupling := by
  obtain ⟨B, hB, hbound⟩ := exists_core_atomicGroundEnergy_upper b hr
  refine ⟨B, hB, fun coupling hc => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hbound coupling hc) (sq_nonneg coupling⁻¹)
  have heq : (coupling⁻¹) ^ 2 * (-coupling ^ 2 + B * coupling) = -1 + B / coupling := by
    field_simp
  rwa [heq] at h

end CuspParameters
end InfiniteZero
