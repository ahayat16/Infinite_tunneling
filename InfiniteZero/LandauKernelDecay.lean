import InfiniteZero.LandauKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exact logarithmic decay of the radial proper-time kernel

The minimum of the real phase determines the logarithmic semiclassical decay.
The estimates here concern the scalar integral `landauKernel`; no operator
resolvent identity is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

theorem landauIntegrand_le_split_action {b h E r α τ : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r)
    (hα1 : α ≤ 1) (hτ : 0 < τ) :
    landauIntegrand b h E r τ ≤
      Real.exp (-((1 - α) * bridgeAction b E r) / h) *
        landauIntegrand b (h / α) E r τ := by
  have hfactor : landauIntegrand b h E r τ =
      Real.exp (-((1 - α) * properTimePhase b E r τ) / h) *
        landauIntegrand b (h / α) E r τ := by
    unfold landauIntegrand
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [hfactor]
  apply mul_le_mul_of_nonneg_right _ (landauIntegrand_pos hb hτ (h / α) E r).le
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (neg_le_neg (mul_le_mul_of_nonneg_left
      (bridgeAction_le_properTimePhase hb hE hr hτ) (sub_nonneg.mpr hα1))) hh.le

/-- Keeping an arbitrary fraction of the phase controls the integral prefactor. -/
theorem landauKernel_le_exp_action {b h E r α : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    landauKernel b h E r ≤ (1 / (Real.pi * E * r ^ 2 * α ^ 2)) *
      Real.exp (-((1 - α) * bridgeAction b E r) / h) := by
  have hhα : 0 < h / α := div_pos hh hα
  have hI : (∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ) ≤
      Real.exp (-((1 - α) * bridgeAction b E r) / h) *
        ∫ τ in Ioi (0 : ℝ), landauIntegrand b (h / α) E r τ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (integrableOn_landauIntegrand hb hh hE hr)
      ((integrableOn_landauIntegrand hb hhα hE hr).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact landauIntegrand_le_split_action hb hh hE hr hα1 hτ
  have hI' := hI.trans (mul_le_mul_of_nonneg_left
    (integral_landauIntegrand_le hb hhα hE hr) (Real.exp_pos _).le)
  have hK := mul_le_mul_of_nonneg_left hI'
    (show 0 ≤ b / (4 * Real.pi * h ^ 2) by positivity)
  unfold landauKernel
  convert hK using 1
  field_simp

/-- An upper exponential bound with an arbitrarily small loss in the action. -/
theorem exists_landauKernel_exp_upper {b E r η : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hη : 0 < η) :
    ∃ C > 0, ∀ h > 0, landauKernel b h E r ≤
      C * Real.exp (-(bridgeAction b E r - η) / h) := by
  have hJ : 0 < bridgeAction b E r := bridgeAction_pos hb.ne' hE hr
  let α : ℝ := min (1 / 2) (η / bridgeAction b E r)
  have hα : 0 < α := lt_min (by norm_num) (div_pos hη hJ)
  have hα1 : α ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hαJ : α * bridgeAction b E r ≤ η :=
    (le_div_iff₀ hJ).1 (min_le_right _ _)
  refine ⟨1 / (Real.pi * E * r ^ 2 * α ^ 2), by positivity, ?_⟩
  intro h hh
  apply (landauKernel_le_exp_action hb hh hE hr hα hα1).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hh.le
  linarith

private theorem exists_properTimePhase_interval {b E r η : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hη : 0 < η) :
    ∃ δ > 0, ∀ τ ∈ Icc (bridgeTime b E r) (bridgeTime b E r + δ),
      properTimePhase b E r τ ≤ bridgeAction b E r + η := by
  have hc := (hasDerivAt_properTimePhase_bridgeTime hb hE hr).continuousAt
  have hnear : ∀ᶠ τ in 𝓝 (bridgeTime b E r),
      properTimePhase b E r τ < bridgeAction b E r + η := by
    have hv : properTimePhase b E r (bridgeTime b E r) < bridgeAction b E r + η := by
      rw [properTimePhase_bridgeTime hb hE hr]
      linarith
    exact hc.tendsto.eventually (gt_mem_nhds hv)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hnear
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro τ hτ
  apply (hball ?_).le
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hτ.1)]
  linarith [hτ.2]

/-- A neighborhood of the phase minimum gives a lower bound with arbitrary action loss. -/
theorem exists_landauKernel_exp_lower {b E r η : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hη : 0 < η) :
    ∃ c > 0, ∀ h > 0, (c / h ^ 2) * Real.exp (-(bridgeAction b E r + η) / h) ≤
      landauKernel b h E r := by
  obtain ⟨δ, hδ, hphase⟩ := exists_properTimePhase_interval hb hE hr hη
  let a := bridgeTime b E r
  have ha : 0 < a := bridgeTime_pos hb hE hr
  have hs : 0 < Real.sinh (b * (a + δ)) :=
    Real.sinh_pos_iff.2 (mul_pos hb (by positivity))
  refine ⟨b * δ / (4 * Real.pi * Real.sinh (b * (a + δ))), by positivity, ?_⟩
  intro h hh
  have hsub : Icc a (a + δ) ⊆ Ioi 0 := fun τ hτ => ha.trans_le hτ.1
  have hi := integrableOn_landauIntegrand hb hh hE hr
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] landauIntegrand b h E r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact (landauIntegrand_pos hb hτ h E r).le
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc a (a + δ)) :
      (Real.sinh (b * (a + δ)))⁻¹ * Real.exp (-(bridgeAction b E r + η) / h) ≤
        landauIntegrand b h E r τ := by
    unfold landauIntegrand
    apply mul_le_mul
    · exact inv_anti₀ (Real.sinh_pos_iff.2 (mul_pos hb (hsub hτ)))
        (Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_left hτ.2 hb.le))
    · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (hphase τ hτ)) hh.le)
    · exact (Real.exp_pos _).le
    · exact (inv_pos.2 (Real.sinh_pos_iff.2 (mul_pos hb (hsub hτ)))).le
  have hI : δ * (Real.sinh (b * (a + δ)))⁻¹ *
      Real.exp (-(bridgeAction b E r + η) / h) ≤
        ∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ := by
    calc
      _ = ∫ _ in Icc a (a + δ), (Real.sinh (b * (a + δ)))⁻¹ *
          Real.exp (-(bridgeAction b E r + η) / h) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring
      _ ≤ ∫ τ in Icc a (a + δ), landauIntegrand b h E r τ :=
        setIntegral_mono_on
          (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
          (hi.mono_set hsub) measurableSet_Icc hpoint
      _ ≤ ∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ :=
        setIntegral_mono_set hi hn (Filter.Eventually.of_forall hsub)
  have hK := mul_le_mul_of_nonneg_left hI
    (show 0 ≤ b / (4 * Real.pi * h ^ 2) by positivity)
  unfold landauKernel
  convert hK using 1
  field_simp

private theorem tendsto_h_log_exp_prefactor {c : ℝ} (hc : 0 < c) (S : ℝ) (N : ℕ) :
    Tendsto (fun h : ℝ => h * Real.log ((c / h ^ N) * Real.exp (-S / h)))
      (𝓝[>] 0) (𝓝 (-S)) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun h : ℝ => h * Real.log h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one)
  have hmodel : Tendsto (fun h : ℝ => h * Real.log c - (h * Real.log h) * (N : ℝ) - S)
      (𝓝[>] 0) (𝓝 (-S)) := by
    simpa only [zero_mul, sub_zero, zero_sub] using
      ((hid.mul_const (Real.log c)).sub (hlog.mul_const (N : ℝ))).sub_const S
  apply hmodel.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  rw [Real.log_mul (div_ne_zero hc.ne' (pow_ne_zero N hhpos.ne'))
      (Real.exp_ne_zero _), Real.log_div hc.ne' (pow_ne_zero N hhpos.ne'),
    Real.log_pow, Real.log_exp]
  field_simp
  ring

/-- The exact exponential rate of the scalar radial proper-time integral. -/
theorem tendsto_h_mul_log_landauKernel {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    Tendsto (fun h : ℝ => h * Real.log (landauKernel b h E r))
      (𝓝[>] 0) (𝓝 (-bridgeAction b E r)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let η : ℝ := (-bridgeAction b E r - a) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨c, hc, hbound⟩ := exists_landauKernel_exp_lower hb hE hr hη
    have hlim := tendsto_h_log_exp_prefactor hc (bridgeAction b E r + η) 2
    have hbetween : a < -(bridgeAction b E r + η) := by dsimp [η]; linarith
    have hevent : ∀ᶠ h : ℝ in 𝓝[>] 0,
        a < h * Real.log ((c / h ^ 2) * Real.exp (-(bridgeAction b E r + η) / h)) :=
      hlim.eventually (lt_mem_nhds hbetween)
    filter_upwards [hevent, self_mem_nhdsWithin] with h hcomp hh
    have hhpos : 0 < h := hh
    apply hcomp.trans_le
    apply mul_le_mul_of_nonneg_left _ hhpos.le
    exact Real.log_le_log (by positivity) (hbound h hhpos)
  · intro a ha
    let η : ℝ := (a + bridgeAction b E r) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨C, hC, hbound⟩ := exists_landauKernel_exp_upper hb hE hr hη
    have hlim : Tendsto (fun h : ℝ =>
        h * Real.log (C * Real.exp (-(bridgeAction b E r - η) / h)))
        (𝓝[>] 0) (𝓝 (-(bridgeAction b E r - η))) := by
      simpa only [pow_zero, div_one] using
        tendsto_h_log_exp_prefactor hC (bridgeAction b E r - η) 0
    have hbetween : -(bridgeAction b E r - η) < a := by dsimp [η]; linarith
    have hevent : ∀ᶠ h : ℝ in 𝓝[>] 0,
        h * Real.log (C * Real.exp (-(bridgeAction b E r - η) / h)) < a :=
      hlim.eventually (gt_mem_nhds hbetween)
    filter_upwards [hevent, self_mem_nhdsWithin] with h hcomp hh
    have hhpos : 0 < h := hh
    apply lt_of_le_of_lt _ hcomp
    apply mul_le_mul_of_nonneg_left _ hhpos.le
    exact Real.log_le_log (landauKernel_pos hb hhpos hE hr) (hbound h hhpos)

end InfiniteZero
