import InfiniteZero.LandauKernelDecay
import InfiniteZero.BridgeActionEnergy
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform logarithmic decay on positive energy-radius rectangles

The constants are uniform in `E ∈ [Emin,Emax]` and `r ∈ [rmin,rmax]`.
For the lower bound, the estimate `∂τ H ≤ Emax` supplies a common interval
width to the right of every minimizer. No compactness admission is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

theorem bridgeTime_le_of_energy_radius_bounds {b Emin rmax E r : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hrmax : 0 < rmax)
    (hE : Emin ≤ E) (hr : r ≤ rmax) :
    bridgeTime b E r ≤ bridgeTime b Emin rmax := by
  unfold bridgeTime
  apply div_le_div_of_nonneg_right _ hb.le
  apply Real.arsinh_le_arsinh.mpr
  apply div_le_div₀ (mul_pos hb hrmax).le (mul_le_mul_of_nonneg_left hr hb.le)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 hEmin))
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by norm_num)

theorem properTimePhase_sub_le_energy_mul {b s τ : ℝ}
    (hb : 0 < b) (hs : 0 < s) (hsτ : s ≤ τ) (E r : ℝ) :
    properTimePhase b E r τ - properTimePhase b E r s ≤ E * (τ - s) := by
  apply (convex_Ioi (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hasDerivAt_properTimePhase hb ht E r).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_properTimePhase hb (interior_subset ht) E r).differentiableAt.differentiableWithinAt)
    (fun t ht => ?_) s hs τ (hs.trans_le hsτ) hsτ
  rw [deriv_properTimePhase hb (interior_subset ht)]
  exact sub_le_self _ (by positivity)

/-- Uniform upper exponential bound for every positive semiclassical parameter. -/
theorem exists_uniform_landauKernel_exp_upper {b Emin Emax rmin rmax η : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) (hη : 0 < η) :
    ∃ C > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rmin rmax, ∀ h > 0,
      landauKernel b h E r ≤ C * Real.exp (-(bridgeAction b E r - η) / h) := by
  have hEm : 0 < Emax := hEmin.trans_le hEmax
  have hrm : 0 < rmax := hrmin.trans_le hrmax
  let Jmax := bridgeAction b Emax rmax
  have hJmax : 0 < Jmax := bridgeAction_pos hb.ne' hEm hrm
  let α : ℝ := min (1 / 2) (η / Jmax)
  have hα : 0 < α := lt_min (by norm_num) (div_pos hη hJmax)
  have hα1 : α ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hαJmax : α * Jmax ≤ η := (le_div_iff₀ hJmax).1 (min_le_right _ _)
  refine ⟨1 / (Real.pi * Emin * rmin ^ 2 * α ^ 2), by positivity, ?_⟩
  intro E hE r hr h hh
  have hEp : 0 < E := hEmin.trans_le hE.1
  have hrp : 0 < r := hrmin.trans_le hr.1
  have hJ : bridgeAction b E r ≤ Jmax :=
    ((strictMono_bridgeAction hb.ne' hEp).monotone hr.2).trans
      (bridgeAction_energy_le hb.ne' hrm hEp hE.2)
  have hαJ : α * bridgeAction b E r ≤ η :=
    (mul_le_mul_of_nonneg_left hJ hα.le).trans hαJmax
  have hC : 1 / (Real.pi * E * r ^ 2 * α ^ 2) ≤
      1 / (Real.pi * Emin * rmin ^ 2 * α ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    · exact hE.1
    · exact hr.1
  apply (landauKernel_le_exp_action hb hh hEp hrp hα hα1).trans
  apply mul_le_mul hC
  · apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hh.le
    linarith
  · exact (Real.exp_pos _).le
  · positivity

/-- Uniform lower exponential bound, with a common interval width `η / Emax`. -/
theorem exists_uniform_landauKernel_exp_lower {b Emin Emax rmin rmax η : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) (hη : 0 < η) :
    ∃ c > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rmin rmax, ∀ h > 0,
      (c / h ^ 2) * Real.exp (-(bridgeAction b E r + η) / h) ≤ landauKernel b h E r := by
  have hEm : 0 < Emax := hEmin.trans_le hEmax
  have hrm : 0 < rmax := hrmin.trans_le hrmax
  let δ := η / Emax
  have hδ : 0 < δ := div_pos hη hEm
  let T := bridgeTime b Emin rmax
  have hT : 0 < T := bridgeTime_pos hb hEmin hrm
  have hs : 0 < Real.sinh (b * (T + δ)) :=
    Real.sinh_pos_iff.2 (mul_pos hb (by positivity))
  refine ⟨b * δ / (4 * Real.pi * Real.sinh (b * (T + δ))), by positivity, ?_⟩
  intro E hE r hr h hh
  have hEp : 0 < E := hEmin.trans_le hE.1
  have hrp : 0 < r := hrmin.trans_le hr.1
  let a := bridgeTime b E r
  have ha : 0 < a := bridgeTime_pos hb hEp hrp
  have haT : a ≤ T := bridgeTime_le_of_energy_radius_bounds hb hEmin hrm hE.1 hr.2
  have hsub : Icc a (a + δ) ⊆ Ioi 0 := fun τ hτ => ha.trans_le hτ.1
  have hphase (τ : ℝ) (hτ : τ ∈ Icc a (a + δ)) :
      properTimePhase b E r τ ≤ bridgeAction b E r + η := by
    have hg := properTimePhase_sub_le_energy_mul hb ha hτ.1 E r
    change properTimePhase b E r τ - properTimePhase b E r (bridgeTime b E r) ≤
      E * (τ - a) at hg
    rw [properTimePhase_bridgeTime hb hEp hrp] at hg
    have hlen : τ - a ≤ δ := by linarith [hτ.2]
    have hδeq : Emax * δ = η := by dsimp [δ]; field_simp
    have hinc := mul_le_mul hE.2 hlen (sub_nonneg.mpr hτ.1) hEm.le
    rw [hδeq] at hinc
    linarith
  have hi := integrableOn_landauIntegrand hb hh hEp hrp
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] landauIntegrand b h E r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact (landauIntegrand_pos hb hτ h E r).le
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc a (a + δ)) :
      (Real.sinh (b * (T + δ)))⁻¹ * Real.exp (-(bridgeAction b E r + η) / h) ≤
        landauIntegrand b h E r τ := by
    unfold landauIntegrand
    apply mul_le_mul
    · exact inv_anti₀ (Real.sinh_pos_iff.2 (mul_pos hb (hsub hτ)))
        (Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hb.le))
    · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (hphase τ hτ)) hh.le)
    · exact (Real.exp_pos _).le
    · exact (inv_pos.2 (Real.sinh_pos_iff.2 (mul_pos hb (hsub hτ)))).le
  have hI : δ * (Real.sinh (b * (T + δ)))⁻¹ *
      Real.exp (-(bridgeAction b E r + η) / h) ≤
        ∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ := by
    calc
      _ = ∫ _ in Icc a (a + δ), (Real.sinh (b * (T + δ)))⁻¹ *
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

/-- The logarithmic action error tends to zero uniformly on the whole rectangle. -/
theorem eventually_uniform_landauKernel_log_error {b Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rmin rmax,
      |h * Real.log (landauKernel b h E r) + bridgeAction b E r| < ε := by
  let η : ℝ := ε / 2
  have hη : 0 < η := half_pos hε
  obtain ⟨C, hC, hu⟩ := exists_uniform_landauKernel_exp_upper hb hEmin hEmax hrmin hrmax hη
  obtain ⟨c, hc, hl⟩ := exists_uniform_landauKernel_exp_lower hb hEmin hEmax hrmin hrmax hη
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun h : ℝ => h * Real.log h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one)
  have huLim : Tendsto (fun h : ℝ => h * Real.log C) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using hid.mul_const (Real.log C)
  have hlLim : Tendsto (fun h : ℝ => h * Real.log c - 2 * (h * Real.log h))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul, mul_zero, sub_zero] using
      (hid.mul_const (Real.log c)).sub (hlog.const_mul 2)
  have huEvent : ∀ᶠ h : ℝ in 𝓝[>] 0, h * Real.log C < η :=
    huLim.eventually (gt_mem_nhds hη)
  have hlEvent : ∀ᶠ h : ℝ in 𝓝[>] 0, -η < h * Real.log c - 2 * (h * Real.log h) :=
    hlLim.eventually (lt_mem_nhds (neg_neg_of_pos hη))
  filter_upwards [huEvent, hlEvent, self_mem_nhdsWithin] with h huSmall hlSmall hh
  have hhpos : 0 < h := hh
  intro E hE r hr
  have hEp : 0 < E := hEmin.trans_le hE.1
  have hrp : 0 < r := hrmin.trans_le hr.1
  have hupper : h * Real.log (landauKernel b h E r) + bridgeAction b E r ≤
      h * Real.log C + η := by
    calc
      _ ≤ h * Real.log (C * Real.exp (-(bridgeAction b E r - η) / h)) +
          bridgeAction b E r := by
        apply add_le_add _ le_rfl
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (landauKernel_pos hb hhpos hEp hrp) (hu E hE r hr h hhpos)) hhpos.le
      _ = _ := by
        rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp]
        field_simp
        ring
  have hlower : h * Real.log c - 2 * (h * Real.log h) - η ≤
      h * Real.log (landauKernel b h E r) + bridgeAction b E r := by
    calc
      _ = h * Real.log ((c / h ^ 2) * Real.exp (-(bridgeAction b E r + η) / h)) +
          bridgeAction b E r := by
        rw [Real.log_mul (div_ne_zero hc.ne' (pow_ne_zero 2 hhpos.ne')) (Real.exp_ne_zero _),
          Real.log_div hc.ne' (pow_ne_zero 2 hhpos.ne'), Real.log_pow, Real.log_exp]
        push_cast
        field_simp
        ring
      _ ≤ _ := by
        apply add_le_add _ le_rfl
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by positivity) (hl E hE r hr h hhpos)) hhpos.le
  apply abs_lt.mpr
  dsimp [η] at *
  constructor <;> linarith

theorem tendstoUniformlyOn_h_log_landauKernel {b Emin Emax rmin rmax : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) :
    TendstoUniformlyOn
      (fun h (p : ℝ × ℝ) => h * Real.log (landauKernel b h p.1 p.2))
      (fun p => -bridgeAction b p.1 p.2) (𝓝[>] 0)
      (Icc Emin Emax ×ˢ Icc rmin rmax) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  filter_upwards [eventually_uniform_landauKernel_log_error hb hEmin hEmax hrmin hrmax hε]
    with h hh
  intro p hp
  have hbound := hh p.1 hp.1 p.2 hp.2
  rw [Real.dist_eq, abs_sub_comm]
  simpa only [sub_neg_eq_add] using hbound

end InfiniteZero
