import InfiniteZero.LogFlatSmooth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Upper bounds for real log-flat Laplace integrals

The estimate is uniform over all slopes above a fixed positive lower bound.
It follows by splitting the logarithmic normal coordinate at a fixed fraction
of `log (1 / h)`. No minimizer, saddle expansion, or integral estimate is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

private theorem eventually_quadratic_le_exponential {B c d : ℝ}
    (hB : 0 < B) (hc : 0 < c) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, B * x ^ 2 ≤ c * Real.exp (d * x) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 2 hd).bound (div_pos hc hB)
  filter_upwards [h] with x hx
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x),
    abs_of_pos (Real.exp_pos _)] at hx
  calc
    B * x ^ 2 ≤ B * ((c / B) * Real.exp (d * x)) :=
      mul_le_mul_of_nonneg_left hx hB.le
    _ = c * Real.exp (d * x) := by field_simp

/-- Pointwise bound with coefficient `β q²`, uniform for every positive
normal coordinate and every slope `a ≥ aMin`. -/
theorem eventually_logFlat_laplace_le_fraction {β tStar aMin q : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (haMin : 0 < aMin)
    (hq : 0 < q) (hq1 : q < 1) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, aMin ≤ a → ∀ t : ℝ, 0 < t →
      Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) ≤
        Real.exp (-(β * q ^ 2) * (Real.log (1 / h)) ^ 2) := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hlarge := hlog.eventually (eventually_quadratic_le_exponential
    (mul_pos hβ (sq_pos_of_pos hq)) (mul_pos haMin hStar) (sub_pos.mpr hq1))
  have hnonneg := hlog.eventually (eventually_ge_atTop (0 : ℝ))
  filter_upwards [hlarge, hnonneg, self_mem_nhdsWithin] with h hlarge hlognonneg hh
  have hhpos : 0 < h := hh
  intro a ha t ht
  let l := Real.log (1 / h)
  let y := Real.log (tStar / t)
  have hl : 0 ≤ l := hlognonneg
  have hapos : 0 < a := lt_of_lt_of_le haMin ha
  have hat : 0 ≤ a * t / h := (div_pos (mul_pos hapos ht) hhpos).le
  apply Real.exp_le_exp.mpr
  change -β * y ^ 2 - a * t / h ≤ -(β * q ^ 2) * l ^ 2
  by_cases hy : q * l ≤ y
  · have hql : 0 ≤ q * l := mul_nonneg hq.le hl
    have hsq : (q * l) ^ 2 ≤ y ^ 2 := by nlinarith
    have hsqβ := mul_le_mul_of_nonneg_left hsq hβ.le
    nlinarith
  · have hyl : (1 - q) * l ≤ l - y := by linarith [lt_of_not_ge hy]
    have hexp : tStar * Real.exp (l - y) = t / h := by
      dsimp [l, y]
      rw [Real.exp_sub, Real.exp_log (div_pos (by norm_num) hhpos),
        Real.exp_log (div_pos hStar ht)]
      field_simp
    have hdom : β * q ^ 2 * l ^ 2 ≤ a * t / h := by
      calc
        β * q ^ 2 * l ^ 2 ≤ aMin * tStar * Real.exp ((1 - q) * l) := hlarge
        _ ≤ aMin * tStar * Real.exp (l - y) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hyl) (mul_pos haMin hStar).le
        _ = aMin * t / h := by rw [mul_assoc, hexp]; ring
        _ ≤ a * t / h := by gcongr
    nlinarith [mul_nonneg hβ.le (sq_nonneg y)]

/-- Any positive loss in the leading Gaussian coefficient is allowed.
The same threshold works for every slope `a ≥ aMin`. -/
theorem eventually_logFlat_laplace_le {β tStar aMin η : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (haMin : 0 < aMin) (hη : 0 < η) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, aMin ≤ a → ∀ t : ℝ, 0 < t →
      Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) ≤
        Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
  let δ : ℝ := min (η / (4 * β)) (1 / 2)
  have hδ : 0 < δ := lt_min (div_pos hη (by positivity)) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδη : δ * (4 * β) ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hq : 0 < 1 - δ := by linarith
  have hq1 : 1 - δ < 1 := by linarith
  have hcoef : β - η ≤ β * (1 - δ) ^ 2 := by
    nlinarith [mul_nonneg hβ.le (sq_nonneg δ)]
  filter_upwards [eventually_logFlat_laplace_le_fraction hβ hStar haMin hq hq1]
    with h hh
  intro a ha t ht
  exact (hh a ha t ht).trans (Real.exp_le_exp.mpr (by
    nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log (1 / h)))]))

/-- The actual positive real integral from the log-flat estimate, with a
natural power of the normal coordinate. The integration domain excludes zero. -/
def logFlatLaplaceIntegral (β tStar t₀ a h : ℝ) (m : ℕ) : ℝ :=
  ∫ t in Ioo 0 t₀, t ^ m *
    Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h)

private theorem logFlat_laplace_integrand_eq (β tStar a h : ℝ) (m : ℕ)
    {t : ℝ} (ht : 0 < t) :
    t ^ m * logFlat β tStar t * Real.exp (-a * t / h) =
      t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) := by
  rw [logFlat_of_pos β tStar ht, mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem continuous_logFlat_laplace_integrand {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (a h : ℝ) (m : ℕ) :
    Continuous (fun t : ℝ => t ^ m * logFlat β tStar t * Real.exp (-a * t / h)) :=
  ((continuous_id.pow m).mul (contDiff_logFlat hβ hStar).continuous).mul
    (((continuous_const.mul continuous_id).div_const h).rexp)

/-- Integrability is proved from the continuous zero extension at the origin. -/
theorem integrableOn_logFlat_laplace {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (t₀ a h : ℝ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ m *
      Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h)) (Ioo 0 t₀) := by
  have hi := ((continuous_logFlat_laplace_integrand hβ hStar a h m).continuousOn.integrableOn_Icc
    (μ := volume) (a := 0) (b := t₀)).mono_set Ioo_subset_Icc_self
  exact hi.congr_fun (fun t ht => logFlat_laplace_integrand_eq β tStar a h m ht.1)
    measurableSet_Ioo

/-- The natural-power integral satisfies the desired bound with explicit
constant `t₀^(m+1)` and no inverse power of `h`. -/
theorem eventually_logFlatLaplaceIntegral_le {β tStar t₀ aMin η : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (haMin : 0 < aMin) (hη : 0 < η) (m : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, aMin ≤ a →
      logFlatLaplaceIntegral β tStar t₀ a h m ≤
        t₀ ^ (m + 1) * Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
  filter_upwards [eventually_logFlat_laplace_le hβ hStar haMin hη] with h hh
  intro a ha
  have hbound (t : ℝ) (ht : t ∈ Ioo 0 t₀) :
      t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h) ≤
        t₀ ^ m * Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
    exact mul_le_mul (pow_le_pow_left₀ ht.1.le ht.2.le m) (hh a ha t ht.1)
      (Real.exp_pos _).le (pow_nonneg ht₀.le m)
  have hconst : IntegrableOn (fun _t : ℝ =>
      t₀ ^ m * Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2)) (Ioo 0 t₀) := by
    exact (continuous_const.continuousOn.integrableOn_Icc (a := 0) (b := t₀)).mono_set
      Ioo_subset_Icc_self
  have hint := setIntegral_mono_on (integrableOn_logFlat_laplace hβ hStar t₀ a h m)
    hconst measurableSet_Ioo hbound
  unfold logFlatLaplaceIntegral
  refine hint.trans_eq ?_
  rw [setIntegral_const, Real.volume_real_Ioo, sub_zero, max_eq_left ht₀.le,
    smul_eq_mul, pow_succ]
  ring

/-- A threshold formulation convenient for later source estimates. -/
theorem exists_logFlatLaplaceIntegral_upper_threshold {β tStar t₀ aMin η : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (haMin : 0 < aMin) (hη : 0 < η) (m : ℕ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ → ∀ a : ℝ, aMin ≤ a →
      logFlatLaplaceIntegral β tStar t₀ a h m ≤
        t₀ ^ (m + 1) * Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
  obtain ⟨h₀, hh₀, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (eventually_logFlatLaplaceIntegral_le hβ hStar ht₀ haMin hη m)
  exact ⟨h₀, hh₀, fun h hh hsmall => hbound ⟨hh, hsmall⟩⟩

/-- The fixed prefactor is absorbed in an arbitrarily small part of the
available loss, giving the upper bound with constant one. -/
theorem eventually_logFlatLaplaceIntegral_le_exp {β tStar t₀ aMin η : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (haMin : 0 < aMin) (hη : 0 < η) (m : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, aMin ≤ a →
      logFlatLaplaceIntegral β tStar t₀ a h m ≤
        Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
  have hlog := tendsto_log_tStar_div_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have hdecay : Tendsto (fun h : ℝ => t₀ ^ (m + 1) *
      Real.exp (-(η / 2) * (Real.log (1 / h)) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_pow_mul_exp_quadratic (half_pos hη) 0 0).comp hlog).const_mul
      (t₀ ^ (m + 1))
  have hsmall := hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_logFlatLaplaceIntegral_le hβ hStar ht₀ haMin (half_pos hη) m,
    hsmall] with h hh hc
  intro a ha
  calc
    logFlatLaplaceIntegral β tStar t₀ a h m ≤
        t₀ ^ (m + 1) * Real.exp (-(β - η / 2) * (Real.log (1 / h)) ^ 2) := hh a ha
    _ = (t₀ ^ (m + 1) * Real.exp (-(η / 2) * (Real.log (1 / h)) ^ 2)) *
        Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc.le (Real.exp_pos
        (-(β - η) * (Real.log (1 / h)) ^ 2)).le

/-- A continuous cutoff bounded above by one preserves the proven estimate.
In particular this applies to the manuscript's smooth cutoff with values in
`[0,1]`. Its value near zero is irrelevant for an upper bound. -/
theorem eventually_logFlat_cutoff_integral_le_exp {β tStar t₀ aMin η : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (haMin : 0 < aMin) (hη : 0 < η) (m : ℕ) {χ : ℝ → ℝ}
    (hχ : Continuous χ) (hχle : ∀ t ∈ Ioo 0 t₀, χ t ≤ 1) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, aMin ≤ a →
      (∫ t in Ioo 0 t₀, χ t * (t ^ m *
        Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h))) ≤
          Real.exp (-(β - η) * (Real.log (1 / h)) ^ 2) := by
  filter_upwards [eventually_logFlatLaplaceIntegral_le_exp hβ hStar ht₀ haMin hη m]
    with h hh
  intro a ha
  have hcont := hχ.mul (continuous_logFlat_laplace_integrand hβ hStar a h m)
  have hint := (hcont.continuousOn.integrableOn_Icc
    (μ := volume) (a := 0) (b := t₀)).mono_set Ioo_subset_Icc_self
  have hint' : IntegrableOn (fun t : ℝ => χ t * (t ^ m *
      Real.exp (-β * (Real.log (tStar / t)) ^ 2 - a * t / h))) (Ioo 0 t₀) :=
    hint.congr_fun (fun t ht => congrArg (fun z => χ t * z)
      (logFlat_laplace_integrand_eq β tStar a h m ht.1)) measurableSet_Ioo
  apply le_trans (setIntegral_mono_on hint'
    (integrableOn_logFlat_laplace hβ hStar t₀ a h m) measurableSet_Ioo ?_) (hh a ha)
  intro t ht
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχle t ht)
    (mul_nonneg (pow_nonneg ht.1.le m) (Real.exp_pos _).le)

end InfiniteZero
