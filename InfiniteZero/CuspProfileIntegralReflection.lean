import InfiniteZero.CuspProfileIntegral
import InfiniteZero.PlaneReflectionMeasure

/-!
# The negative cusp has the same integral profile bounds

Reflection transports the actual source and its support to the positive
cusp and preserves the physical planar volume. Consequently both the exact
normal moment and the uniform logarithmic threshold are unchanged.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

private theorem support_comp_reflection_subset_cuspPlus {p : CuspParameters}
    {F : Wavefunction} (hsupport : Function.support F ⊆ Function.support p.cuspMinus) :
    Function.support (F ∘ reflection) ⊆ Function.support p.cuspPlus := by
  intro x hx
  exact (reflection_mem_cuspMinus_support_iff p x).mp (hsupport hx)

theorem integral_norm_le_cuspMinus_profile
    {p : CuspParameters} (hp : p.BasicConditions) {β : ℝ} (hβ : 0 < β)
    {F : Wavefunction} (hF : Continuous F)
    (hsupport : Function.support F ⊆ Function.support p.cuspMinus)
    {B a h : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ tsupport p.cuspMinus,
      ‖F x‖ ≤ B * logFlat β p.tStar (p.normalCoordinate (reflection x)) *
        Real.exp (-a * p.normalCoordinate (reflection x) / h)) :
    Integrable F ∧ (∫ x : Plane, ‖F x‖) ≤
      (2 * p.s₀) * B * logFlatLaplaceIntegral β p.tStar p.t₀ a h 2 := by
  obtain ⟨hFi, hI⟩ := integral_norm_le_cuspPlus_profile hp hβ
    (hF.comp reflectionLinearIsometryEquiv.continuous)
    (support_comp_reflection_subset_cuspPlus hsupport) hB (a := a) (h := h) (by
      intro x hx
      simpa only [Function.comp_apply, reflection_involutive] using
        hbound (reflection x) ((reflection_mem_cuspMinus_tsupport_iff p x).mpr hx))
  refine ⟨(integrable_comp_reflection_iff F).mp hFi, ?_⟩
  exact (integral_comp_reflection (fun x => ‖F x‖)).symm.le.trans hI

/-- The same threshold works after reflection; it is chosen before the
coupling, positive slope, source amplitude and continuous source itself. -/
theorem exists_cuspMinus_profile_integral_threshold
    {p : CuspParameters} (hp : p.BasicConditions) {β' β aMin : ℝ}
    (hβ' : 0 < β') (hβ'β : β' < β) (haMin : 0 < aMin) :
    ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling → ∀ a : ℝ, aMin ≤ a →
      ∀ B : ℝ, 0 ≤ B → ∀ F : Wavefunction, Continuous F →
      Function.support F ⊆ Function.support p.cuspMinus →
      (∀ x ∈ tsupport p.cuspMinus,
        ‖F x‖ ≤ B * logFlat β p.tStar (p.normalCoordinate (reflection x)) *
          Real.exp (-a * coupling * p.normalCoordinate (reflection x))) →
      Integrable F ∧ (∫ x : Plane, ‖F x‖) ≤
        (2 * p.s₀) * B * Real.exp (-β' * (Real.log coupling) ^ 2) := by
  obtain ⟨N, hN, hplus⟩ := exists_cuspPlus_profile_integral_threshold hp hβ' hβ'β haMin
  refine ⟨N, hN, ?_⟩
  intro coupling hc a ha B hB F hF hsupport hbound
  obtain ⟨hFi, hI⟩ := hplus coupling hc a ha B hB (F ∘ reflection)
    (hF.comp reflectionLinearIsometryEquiv.continuous)
    (support_comp_reflection_subset_cuspPlus hsupport) (by
      intro x hx
      simpa only [Function.comp_apply, reflection_involutive] using
        hbound (reflection x) ((reflection_mem_cuspMinus_tsupport_iff p x).mpr hx))
  refine ⟨(integrable_comp_reflection_iff F).mp hFi, ?_⟩
  exact (integral_comp_reflection (fun x => ‖F x‖)).symm.le.trans hI

end InfiniteZero.CuspParameters
