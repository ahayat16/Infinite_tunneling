import InfiniteZero.LogFlatIntegral
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Lower bounds and the logarithmic rate of real log-flat integrals

For the leading logarithmic rate it suffices to integrate on `(h, 2*h)`.
This avoids any saddle-location hypothesis. All estimates are uniform for
slopes in a fixed positive compact interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

private theorem eventually_affine_le_quadratic {η : ℝ} (hη : 0 < η) (A B : ℝ) :
    ∀ᶠ x : ℝ in atTop, A * x + B ≤ η * x ^ 2 := by
  have hd : Tendsto (fun x : ℝ => Real.exp (-η * x ^ 2 + A * x + B)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, zero_mul, ← Real.exp_add] using
      (tendsto_pow_mul_exp_quadratic hη A 0).mul_const (Real.exp B)
  filter_upwards [hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx
  have he := Real.exp_lt_one_iff.mp hx
  linarith

/-- An explicit lower bound obtained by restricting the integral to `(h,2h)`.
No positivity of the actual slope is needed for this lower estimate. -/
theorem logFlatLaplaceIntegral_lower_interval {β tStar t₀ aMax a h : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (haMax : 0 < aMax)
    (hh : 0 < h) (hsmall : 2 * h ≤ min t₀ tStar) (ha : a ≤ aMax) (m : ℕ) :
    h ^ (m + 1) * Real.exp (-β * (Real.log tStar + Real.log (1 / h)) ^ 2 - 2 * aMax) ≤
      logFlatLaplaceIntegral β tStar t₀ a h m := by
  let K := Real.exp (-β * (Real.log tStar + Real.log (1 / h)) ^ 2 - 2 * aMax)
  have hsub : Ioo h (2 * h) ⊆ Ioo 0 t₀ :=
    Ioo_subset_Ioo hh.le (le_trans hsmall (min_le_left _ _))
  have hint := integrableOn_logFlat_laplace hβ hStar t₀ a h m
  have hintSmall := hint.mono_set hsub
  have hpoint (t : ℝ) (ht : t ∈ Ioo h (2 * h)) :
      h ^ m * K ≤ t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) := by
    have htpos : 0 < t := lt_trans hh ht.1
    have htle : t ≤ tStar := ht.2.le.trans (hsmall.trans (min_le_right _ _))
    have hy0 : 0 ≤ Real.log (tStar / t) := Real.log_nonneg ((one_le_div htpos).mpr htle)
    have hy : Real.log (tStar / t) ≤ Real.log tStar + Real.log (1 / h) := by
      calc
        Real.log (tStar / t) ≤ Real.log (tStar / h) :=
          Real.log_le_log (div_pos hStar htpos) (div_le_div_of_nonneg_left hStar.le hh ht.1.le)
        _ = Real.log tStar + Real.log (1 / h) := by
          rw [Real.log_div hStar.ne' hh.ne']
          simp [sub_eq_add_neg]
    have hsq : (Real.log (tStar / t)) ^ 2 ≤
        (Real.log tStar + Real.log (1 / h)) ^ 2 := by nlinarith
    have hlinear : a * t / h ≤ 2 * aMax := by
      calc
        a * t / h ≤ aMax * t / h := by gcongr
        _ ≤ aMax * (2 * h) / h := by gcongr; exact ht.2.le
        _ = 2 * aMax := by field_simp
    have he : K ≤ Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hβ.le]
    exact mul_le_mul (pow_le_pow_left₀ hh.le ht.1.le m) he (Real.exp_pos _).le
      (pow_nonneg htpos.le m)
  have hconst : IntegrableOn (fun _t : ℝ => h ^ m * K) (Ioo h (2 * h)) := by
    exact (continuous_const.continuousOn.integrableOn_Icc
      (a := h) (b := 2 * h)).mono_set Ioo_subset_Icc_self
  have hfirst := setIntegral_mono_on hconst hintSmall measurableSet_Ioo hpoint
  have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 t₀), 0 ≤
      t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      mul_nonneg (pow_nonneg ht.1.le m) (Real.exp_pos _).le
  have hsecond := setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall hsub)
  change _ ≤ ∫ t in Ioo 0 t₀, t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h)
  calc
    _ = ∫ _t in Ioo h (2 * h), h ^ m * K := by
      rw [setIntegral_const, Real.volume_real_Ioo,
        show 2 * h - h = h by ring, max_eq_left hh.le, smul_eq_mul, pow_succ]
      ring
    _ ≤ _ := hfirst.trans hsecond

/-- The lower logarithmic bound is uniform over all slopes bounded above by
`aMax`; in particular it is uniform on the compact slope interval of L2.8. -/
theorem eventually_exp_le_logFlatLaplaceIntegral {β tStar t₀ aMax η : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (haMax : 0 < aMax) (hη : 0 < η) (m : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, a ≤ aMax →
      Real.exp (-(β + η) * (Real.log (1 / h)) ^ 2) ≤
        logFlatLaplaceIntegral β tStar t₀ a h m := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have habsorb := hlog.eventually (eventually_affine_le_quadratic hη
    ((m + 1 : ℕ) + 2 * β * Real.log tStar) (β * (Real.log tStar) ^ 2 + 2 * aMax))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < min t₀ tStar / 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (half_pos (lt_min ht₀ hStar)))
  filter_upwards [habsorb, hsmall, self_mem_nhdsWithin] with h habsorb hsmall hh
  have hhpos : 0 < h := hh
  intro a ha
  have hpow : h ^ (m + 1) = Real.exp (-((m + 1 : ℕ) : ℝ) * Real.log (1 / h)) := by
    simp only [one_div, Real.log_inv, neg_mul, mul_neg, neg_neg]
    rw [Real.exp_nat_mul, Real.exp_log hhpos]
  apply le_trans _ (logFlatLaplaceIntegral_lower_interval hβ hStar haMax hhpos
    (by linarith) ha m)
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The same lower bound with the manuscript's cutoff: nonnegative, at most
one, continuous, and equal to one on some right neighborhood of zero. -/
theorem eventually_exp_le_logFlat_cutoff_integral {β tStar t₀ aMax η : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (haMax : 0 < aMax) (hη : 0 < η) (m : ℕ) {χ : ℝ → ℝ}
    (hχ : Continuous χ) (hχrange : ∀ t ∈ Ioo 0 t₀, χ t ∈ Icc (0 : ℝ) 1)
    (hχone : χ =ᶠ[𝓝[>] 0] fun _ => 1) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, a ≤ aMax →
      Real.exp (-(β + η) * (Real.log (1 / h)) ^ 2) ≤
        ∫ t in Ioo 0 t₀, χ t * (t ^ m *
          Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h)) := by
  obtain ⟨r₀, hr₀, hone⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hχone
  let r := min t₀ r₀
  have hr : 0 < r := lt_min ht₀ hr₀
  have hsub : Ioo 0 r ⊆ Ioo 0 t₀ := Ioo_subset_Ioo le_rfl (min_le_left _ _)
  filter_upwards [eventually_exp_le_logFlatLaplaceIntegral hβ hStar hr haMax hη m]
    with h hh
  intro a ha
  have hint := integrableOn_logFlat_laplace hβ hStar t₀ a h m
  have hχbounded : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 t₀), ‖χ t‖ ≤ (1 : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχrange t ht).1]
      exact (hχrange t ht).2
  have hintχ := hint.bdd_mul hχ.aestronglyMeasurable hχbounded
  have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 t₀), 0 ≤ χ t * (t ^ m *
      Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h)) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      mul_nonneg (hχrange t ht).1 (mul_nonneg (pow_nonneg ht.1.le m) (Real.exp_pos _).le)
  calc
    _ ≤ logFlatLaplaceIntegral β tStar r a h m := hh a ha
    _ = ∫ t in Ioo 0 r, χ t * (t ^ m *
        Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [hone ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩, one_mul]
    _ ≤ _ := setIntegral_mono_set hintχ hnonneg (Filter.Eventually.of_forall hsub)

/-- The logarithm of the integral has leading coefficient `-β`, uniformly
over each fixed compact interval of positive slopes. -/
theorem tendstoUniformlyOn_logFlatLaplaceIntegral_log_ratio {β tStar t₀ aMin aMax : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (haMin : 0 < aMin) (hinterval : aMin ≤ aMax) (m : ℕ) :
    TendstoUniformlyOn
      (fun h a : ℝ => Real.log (logFlatLaplaceIntegral β tStar t₀ a h m) /
        (Real.log (1 / h)) ^ 2)
      (fun _a => -β) (𝓝[>] 0) (Icc aMin aMax) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have haMax : 0 < aMax := haMin.trans_le hinterval
  filter_upwards [eventually_exp_le_logFlatLaplaceIntegral hβ hStar ht₀ haMax (half_pos hε) m,
    eventually_logFlatLaplaceIntegral_le_exp hβ hStar ht₀ haMin (half_pos hε) m,
    hlog.eventually (eventually_gt_atTop (0 : ℝ))] with h hlow hupp hlogpos
  intro a ha
  have hIpos : 0 < logFlatLaplaceIntegral β tStar t₀ a h m :=
    (Real.exp_pos _).trans_le (hlow a ha.2)
  have hlowLog := Real.log_le_log (Real.exp_pos _) (hlow a ha.2)
  have huppLog := Real.log_le_log hIpos (hupp a ha.1)
  rw [Real.log_exp] at hlowLog huppLog
  have hsq : 0 < (Real.log (1 / h)) ^ 2 := sq_pos_of_pos hlogpos
  have hlo : -(β + ε / 2) ≤ Real.log (logFlatLaplaceIntegral β tStar t₀ a h m) /
      (Real.log (1 / h)) ^ 2 := (le_div_iff₀ hsq).mpr hlowLog
  have hup : Real.log (logFlatLaplaceIntegral β tStar t₀ a h m) /
      (Real.log (1 / h)) ^ 2 ≤ -(β - ε / 2) := (div_le_iff₀ hsq).mpr huppLog
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem tendsto_logFlatLaplaceIntegral_log_ratio {β tStar t₀ a : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀) (ha : 0 < a) (m : ℕ) :
    Tendsto (fun h : ℝ => Real.log (logFlatLaplaceIntegral β tStar t₀ a h m) /
      (Real.log (1 / h)) ^ 2) (𝓝[>] 0) (𝓝 (-β)) :=
  (tendstoUniformlyOn_logFlatLaplaceIntegral_log_ratio hβ hStar ht₀ ha le_rfl m).tendsto_at
    ⟨le_rfl, le_rfl⟩

end InfiniteZero
