import InfiniteZero.InactiveSupportGaps
import InfiniteZero.LandauKernelUniform
import InfiniteZero.HoppingIntegrability

/-!
# Uniform exponential kernel bounds for the seven inactive supports

The constant is uniform in the bridge energy on a fixed positive compact
interval, the reference energy in `(0,2]`, all support points, and every
positive semiclassical parameter. The only fixed geometric choice is `L`.
The final lemmas bound an actual source pairing by the two source L¹ norms.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero
namespace CuspParameters

/-- The three bounds cover one core-core, four ordered mixed, and two
same-cusp support pairs. All quantities are the explicit scalar Landau kernel. -/
structure InactiveKernelUpperBounds (p : CuspParameters) (L Emin Emax η C : ℝ) : Prop where
  core_core : ∀ E ∈ Icc Emin Emax, ∀ E₀ ∈ Ioc (0 : ℝ) 2,
    ∀ z ∈ tsupport p.core, ∀ w ∈ tsupport p.core, ∀ h > 0,
      landauKernel p.b h E ‖z + w - 2 • displacement L‖ ≤ C * Real.exp
        (-(bridgeAction p.b E (Geometry.activeDistance p.R L) +
          2 * bridgeAction p.b E₀ p.R + 32 * p.hopMargin - η) / h)
  mixed : ∀ E ∈ Icc Emin Emax, ∀ E₀ ∈ Ioc (0 : ℝ) 2, ∀ z w : Plane,
    ((z ∈ tsupport p.core ∧ w ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus) ∨
      (w ∈ tsupport p.core ∧ z ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus)) →
    ∀ h > 0,
      landauKernel p.b h E ‖z + w - 2 • displacement L‖ ≤ C * Real.exp
        (-(bridgeAction p.b E (Geometry.activeDistance p.R L) +
          bridgeAction p.b E₀ p.R + 32 * p.hopMargin - η) / h)
  same_cusp : ∀ E ∈ Icc Emin Emax, ∀ z w : Plane,
    ((z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspPlus) ∨
      (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspMinus)) →
    ∀ h > 0,
      landauKernel p.b h E ‖z + w - 2 • displacement L‖ ≤ C * Real.exp
        (-(bridgeAction p.b E (Geometry.activeDistance p.R L) + 48 * p.hopMargin - η) / h)

theorem SeparationCertificate.exists_uniform_support_kernel_exp_upper {p : CuspParameters}
    (cert : p.SeparationCertificate) (hp : p.BasicConditions) {L Emin Emax η : ℝ}
    (hL : cert.L₀ ≤ L) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax) (hη : 0 < η) :
    ∃ C > 0, ∀ E ∈ Icc Emin Emax, ∀ z w : Plane,
      z ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus →
      w ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus → ∀ h > 0,
      landauKernel p.b h E ‖z + w - 2 • displacement L‖ ≤
        C * Real.exp (-(bridgeAction p.b E ‖z + w - 2 • displacement L‖ - η) / h) := by
  have haL : cert.supportRadius < L :=
    (lt_of_le_of_lt (le_max_left cert.supportRadius p.R) cert.separation).trans_le hL
  obtain ⟨C, hC, hbound⟩ := exists_uniform_landauKernel_exp_upper hp.b_pos hEmin hEmax
    (show 0 < 2 * (L - cert.supportRadius) by linarith)
    (show 2 * (L - cert.supportRadius) ≤ 2 * (L + cert.supportRadius) by
      linarith [cert.supportRadius_pos]) hη
  refine ⟨C, hC, ?_⟩
  intro E hE z w hz hw h hh
  exact hbound E hE _ (cert.component_support_annulus hp hL hz hw).2 h hh

/-- A single uniform constant works for every inactive support pair and both
energy parameters, with the exact geometric margins proved in T5.5. -/
theorem exists_inactiveKernelUpperBounds {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L Emin Emax η : ℝ}
    (hL : cert.L₀ ≤ L) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax) (hη : 0 < η) :
    ∃ C > 0, InactiveKernelUpperBounds p L Emin Emax η C := by
  obtain ⟨C, hC, hbound⟩ := cert.exists_uniform_support_kernel_exp_upper hp hL hEmin hEmax hη
  have hexp {h A B : ℝ} (hh : 0 < h) (hAB : A ≤ B) :
      C * Real.exp (-(B - η) / h) ≤ C * Real.exp (-(A - η) / h) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  refine ⟨C, hC, ⟨?_, ?_, ?_⟩⟩
  · intro E hE E₀ hE₀ z hz w hw h hh
    apply (hbound E hE z w (Or.inl (Or.inl hz)) (Or.inl (Or.inl hw)) h hh).trans
    apply hexp hh
    have hg := core_core_action_gap hp cert hL (hEmin.trans_le hE.1) hE₀.1 hE₀.2 hz hw
    dsimp [activeReferenceAction] at hg
    linarith
  · intro E hE E₀ hE₀ z w hzw h hh
    have hsup : z ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus ∧
        w ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus := by
      rcases hzw with ⟨hz, hw | hw⟩ | ⟨hw, hz | hz⟩
      · exact ⟨Or.inl (Or.inl hz), Or.inl (Or.inr hw)⟩
      · exact ⟨Or.inl (Or.inl hz), Or.inr hw⟩
      · exact ⟨Or.inl (Or.inr hz), Or.inl (Or.inl hw)⟩
      · exact ⟨Or.inr hz, Or.inl (Or.inl hw)⟩
    apply (hbound E hE z w hsup.1 hsup.2 h hh).trans
    apply hexp hh
    have hg : p.activeReferenceAction L E E₀ + 32 * p.hopMargin ≤
        bridgeAction p.b E₀ p.R + bridgeAction p.b E ‖z + w - 2 • displacement L‖ := by
      rcases hzw with ⟨hz, hw⟩ | ⟨hw, hz⟩
      · exact core_cusp_action_gap hp cert hL (hEmin.trans_le hE.1) hE₀.1 hE₀.2 hz hw
      · exact cusp_core_action_gap hp cert hL (hEmin.trans_le hE.1) hE₀.1 hE₀.2 hz hw
    dsimp [activeReferenceAction] at hg
    linarith
  · intro E hE z w hzw h hh
    have hsup : z ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus ∧
        w ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus := by
      rcases hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
      · exact ⟨Or.inl (Or.inr hz), Or.inl (Or.inr hw)⟩
      · exact ⟨Or.inr hz, Or.inr hw⟩
    apply (hbound E hE z w hsup.1 hsup.2 h hh).trans
    apply hexp hh
    have hRL := cert.radius_lt hL
    have hg := same_cusp_action_gap hp (show p.R ≤ 2 * L by linarith [hp.radius_pos])
      (hEmin.trans_le hE.1) hzw
    linarith

end CuspParameters

/-- The bound is only required where both sources are nonzero. -/
theorem norm_channelIntegrand_le {K : Plane → Plane → ℂ} {F G : Wavefunction} {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ z ∈ Function.support F, ∀ w ∈ Function.support G, ‖K z w‖ ≤ C)
    (q : Plane × Plane) :
    ‖channelIntegrand K F G q‖ ≤ C * (‖F q.1‖ * ‖G q.2‖) := by
  by_cases hF : F q.1 = 0
  · calc
      _ = 0 := by simp [channelIntegrand, hF]
      _ ≤ _ := mul_nonneg hC (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  by_cases hG : G q.2 = 0
  · simp [channelIntegrand, hG]
  have hk := hbound q.1 hF q.2 hG
  simp only [channelIntegrand, norm_mul, norm_star]
  nlinarith only [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (norm_nonneg (F q.1))) (norm_nonneg (G q.2))]

theorem channelIntegrand_integrable_of_bound {K : Plane → Plane → ℂ} {F G : Wavefunction}
    {C : ℝ} (hC : 0 ≤ C) (hF : Integrable F) (hG : Integrable G)
    (hK : Measurable (fun q : Plane × Plane => K q.1 q.2))
    (hbound : ∀ z ∈ Function.support F, ∀ w ∈ Function.support G, ‖K z w‖ ≤ C) :
    Integrable (channelIntegrand K F G) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (channelIntegrand K F G) (volume.prod volume) := by
    have hFm : AEStronglyMeasurable (fun q : Plane × Plane => star (F q.1))
        (volume.prod volume) := by
      simpa only [Complex.star_def] using
        Complex.continuous_conj.comp_aestronglyMeasurable hF.aestronglyMeasurable.comp_fst
    exact (hFm.mul hK.aestronglyMeasurable).mul hG.aestronglyMeasurable.comp_snd
  exact ((hF.norm.mul_prod hG.norm).const_mul C).mono' hm
    (Filter.Eventually.of_forall (norm_channelIntegrand_le hC hbound))

/-- An absolute bound for the concrete double integral in a source pairing.
The two factors on the right are the ordinary L¹ norms of the sources. -/
theorem norm_sourcePairing_le (h : ℝ) {K : Plane → Plane → ℂ} {F G : Wavefunction}
    {C : ℝ} (hC : 0 ≤ C) (hF : Integrable F) (hG : Integrable G)
    (hK : Measurable (fun q : Plane × Plane => K q.1 q.2))
    (hbound : ∀ z ∈ Function.support F, ∀ w ∈ Function.support G, ‖K z w‖ ≤ C) :
    ‖sourcePairing h K F G‖ ≤
      h ^ 2 * C * (∫ z : Plane, ‖F z‖) * (∫ w : Plane, ‖G w‖) := by
  have hi := channelIntegrand_integrable_of_bound hC hF hG hK hbound
  have hmajor := (hF.norm.mul_prod hG.norm).const_mul C
  have hb : (∫ q : Plane × Plane, ‖channelIntegrand K F G q‖ ∂volume.prod volume) ≤
      C * (∫ z : Plane, ‖F z‖) * (∫ w : Plane, ‖G w‖) := by
    calc
      _ ≤ ∫ q : Plane × Plane, C * (‖F q.1‖ * ‖G q.2‖) ∂volume.prod volume :=
        integral_mono_ae hi.norm hmajor
          (Filter.Eventually.of_forall (norm_channelIntegrand_le hC hbound))
      _ = _ := by
        rw [integral_const_mul,
          integral_prod_mul (fun z : Plane => ‖F z‖) (fun w : Plane => ‖G w‖)]
        ring
  calc
    ‖sourcePairing h K F G‖ = h ^ 2 *
        ‖∫ q : Plane × Plane, channelIntegrand K F G q ∂volume.prod volume‖ := by
      simp [sourcePairing, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ h ^ 2 * (∫ q : Plane × Plane, ‖channelIntegrand K F G q‖ ∂volume.prod volume) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (sq_nonneg h)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hb (sq_nonneg h)]

/-- Specialization to the actual magnetic source kernel. The scalar radial
bound suffices because the magnetic phase has norm one. -/
theorem norm_sourcePairing_sourceKernel_le {b L h E C : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hC : 0 ≤ C)
    {F G : Wavefunction} (hF : Integrable F) (hG : Integrable G)
    (hr : ∀ z ∈ Function.support F, ∀ w ∈ Function.support G,
      0 < ‖z + w - 2 • displacement L‖)
    (hbound : ∀ z ∈ Function.support F, ∀ w ∈ Function.support G,
      landauKernel b h E ‖z + w - 2 • displacement L‖ ≤ C) :
    ‖sourcePairing h (sourceKernel b L h E) F G‖ ≤
      h ^ 2 * C * (∫ z : Plane, ‖F z‖) * (∫ w : Plane, ‖G w‖) := by
  apply norm_sourcePairing_le h hC hF hG (measurable_sourceKernel b L h E)
  intro z hz w hw
  rw [norm_sourceKernel hb hh hE L z w (hr z hz w hw)]
  exact hbound z hz w hw

end InfiniteZero
