import InfiniteZero.CuspChartJacobian
import InfiniteZero.ConstructionCompact

/-!
# Integrating a profile on the genuine positive cusp

Support localization, the exact chart Jacobian and the scalar log-flat
moment give an actual L¹ bound. All thresholds are uniform in the source,
its amplitude and the positive normal slope.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero.CuspParameters

/-- A continuous source supported on the positive cusp is integrable, and
its profile integrates with the exact Jacobian moment of order two. -/
theorem integral_norm_le_cuspPlus_profile
    {p : CuspParameters} (hp : p.BasicConditions) {β : ℝ} (hβ : 0 < β)
    {F : Wavefunction} (hF : Continuous F)
    (hsupport : Function.support F ⊆ Function.support p.cuspPlus)
    {B a h : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ tsupport p.cuspPlus,
      ‖F x‖ ≤ B * logFlat β p.tStar (p.normalCoordinate x) *
        Real.exp (-a * p.normalCoordinate x / h)) :
    Integrable F ∧ (∫ x : Plane, ‖F x‖) ≤
      (2 * p.s₀) * B * logFlatLaplaceIntegral β p.tStar p.t₀ a h 2 := by
  have hcompact : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact (cuspPlus_hasCompactSupport hp)
      (hsupport.trans (subset_tsupport _))
  refine ⟨hF.integrable_of_hasCompactSupport hcompact, ?_⟩
  have hchart : Continuous p.cuspChart := p.cuspChart_contDiff.continuous
  have hStar : 0 < p.tStar := hp.t₀_pos.trans hp.t₀_lt
  have hfint : IntegrableOn (fun q : ℝ × ℝ => q.1 ^ 2 * ‖F (p.cuspChart q)‖)
      p.cuspChartDomain := by
    have hc : Continuous (fun q : ℝ × ℝ => q.1 ^ 2 * ‖F (p.cuspChart q)‖) :=
      (continuous_fst.pow 2).mul (hF.comp hchart).norm
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hgcont : Continuous (fun q : ℝ × ℝ => B *
      (q.1 ^ 2 * logFlat β p.tStar q.1 * Real.exp (-a * q.1 / h))) := by
    exact continuous_const.mul (((continuous_fst.pow 2).mul
      ((contDiff_logFlat hβ hStar).continuous.comp continuous_fst)).mul
        ((continuous_const.mul continuous_fst).div_const h).rexp)
  have hgint : IntegrableOn (fun q : ℝ × ℝ => B *
      (q.1 ^ 2 * logFlat β p.tStar q.1 * Real.exp (-a * q.1 / h)))
      p.cuspChartDomain :=
    (hgcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hreduce : (∫ x : Plane, ‖F x‖) = ∫ q in p.cuspChartDomain,
      q.1 ^ 2 * ‖F (p.cuspChart q)‖ := by
    have he : (∫ x in p.cuspChart '' p.cuspChartDomain, ‖F x‖) = ∫ x : Plane, ‖F x‖ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : F x = 0 := by
        by_contra hn
        exact hx (p.cuspPlus_support_subset_chartImage (hsupport hn))
      simp only [hz, norm_zero]
    rw [← he]
    simpa only [smul_eq_mul] using p.integral_image_cuspChart
      (s := p.cuspChartDomain) (measurableSet_Ioo.prod measurableSet_Ioo)
      (fun _ hq => hq.1.1) (fun x => ‖F x‖)
  rw [hreduce]
  calc
    _ ≤ ∫ q in p.cuspChartDomain, B *
        (q.1 ^ 2 * logFlat β p.tStar q.1 * Real.exp (-a * q.1 / h)) := by
      apply setIntegral_mono_on hfint hgint (measurableSet_Ioo.prod measurableSet_Ioo)
      intro q _hq
      have hb : ‖F (p.cuspChart q)‖ ≤ B * logFlat β p.tStar q.1 * Real.exp (-a * q.1 / h) := by
        by_cases hz : F (p.cuspChart q) = 0
        · rw [hz, norm_zero]
          exact mul_nonneg (mul_nonneg hB (by unfold logFlat; split <;> positivity)) (Real.exp_pos _).le
        · simpa only [normalCoordinate_cuspChart] using
            hbound _ ((subset_tsupport p.cuspPlus) (hsupport hz))
      calc
        _ ≤ q.1 ^ 2 * (B * logFlat β p.tStar q.1 * Real.exp (-a * q.1 / h)) :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg _)
        _ = _ := by ring
    _ = ∫ q in p.cuspChartDomain, B * ((q.1 ^ 2 *
        Real.exp (-β * (Real.log (p.tStar / q.1)) ^ 2 - a * q.1 / h)) * (1 : ℝ)) := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro q hq
      dsimp only
      rw [logFlat_of_pos β p.tStar hq.1.1]
      rw [mul_assoc (q.1 ^ 2), ← Real.exp_add]
      simp only [sub_eq_add_neg, mul_one, neg_mul, neg_div]
    _ = _ := by
      rw [integral_const_mul, cuspChartDomain, Measure.volume_eq_prod ℝ ℝ,
        setIntegral_prod_mul (fun t : ℝ => t ^ 2 *
          Real.exp (-β * (Real.log (p.tStar / t)) ^ 2 - a * t / h))
          (fun _ : ℝ => (1 : ℝ)) (Ioo 0 p.t₀) (Ioo (-p.s₀) p.s₀)
          (μ := volume) (ν := volume)]
      rw [setIntegral_const, Real.volume_real_Ioo, smul_eq_mul,
        max_eq_left (by linarith [hp.s₀_pos] : 0 ≤ p.s₀ - -p.s₀)]
      unfold logFlatLaplaceIntegral
      ring

/-- The threshold is selected before the coupling, slope, amplitude and
continuous source. The fixed normal moment prefactor is absorbed by the
strict loss in the log-flat coefficient. -/
theorem exists_cuspPlus_profile_integral_threshold
    {p : CuspParameters} (hp : p.BasicConditions) {β' β aMin : ℝ}
    (hβ' : 0 < β') (hβ'β : β' < β) (haMin : 0 < aMin) :
    ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling → ∀ a : ℝ, aMin ≤ a →
      ∀ B : ℝ, 0 ≤ B → ∀ F : Wavefunction, Continuous F →
      Function.support F ⊆ Function.support p.cuspPlus →
      (∀ x ∈ tsupport p.cuspPlus,
        ‖F x‖ ≤ B * logFlat β p.tStar (p.normalCoordinate x) *
          Real.exp (-a * coupling * p.normalCoordinate x)) →
      Integrable F ∧ (∫ x : Plane, ‖F x‖) ≤
        (2 * p.s₀) * B * Real.exp (-β' * (Real.log coupling) ^ 2) := by
  have he := eventually_logFlatLaplaceIntegral_le_exp (hβ'.trans hβ'β)
    (hp.t₀_pos.trans hp.t₀_lt) hp.t₀_pos haMin (sub_pos.mpr hβ'β) 2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (tendsto_inv_atTop_nhdsGT_zero.eventually he)
  refine ⟨max N 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro coupling hc a ha B hB F hF hsupport hbound
  obtain ⟨hFi, hbase⟩ := integral_norm_le_cuspPlus_profile hp (hβ'.trans hβ'β)
    hF hsupport hB (a := a) (h := coupling⁻¹) (by
      intro x hx
      have heq : -a * p.normalCoordinate x / coupling⁻¹ =
          -a * coupling * p.normalCoordinate x := by rw [div_inv_eq_mul]; ring
      simpa only [heq] using hbound x hx)
  refine ⟨hFi, hbase.trans ?_⟩
  have hi := hN coupling ((le_max_left _ _).trans hc) a ha
  have hi' : logFlatLaplaceIntegral β p.tStar p.t₀ a coupling⁻¹ 2 ≤
      Real.exp (-β' * (Real.log coupling) ^ 2) := by
    simpa only [sub_sub_cancel, one_div, inv_inv] using hi
  exact mul_le_mul_of_nonneg_left hi' (mul_nonneg (mul_nonneg (by norm_num) hp.s₀_pos.le) hB)

end InfiniteZero.CuspParameters
