import InfiniteZero.LogFlatActiveRealTail
import InfiniteZero.LogFlatPolynomialErrors
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Removing the complement of the real active normal box

The estimate uses only the genuine radial gain, before complex deformation.
Outside the smaller box, at least one normal coordinate is large. The
result keeps a stretched exponential which absorbs the two saddle
normalizers and any fixed polynomial semiclassical loss.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def positiveNormalBox (a : ℝ) : Set (ℝ × ℝ) := Ioo 0 a ×ˢ Ioo 0 a

theorem measurableSet_positiveNormalBox (a : ℝ) : MeasurableSet (positiveNormalBox a) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem positiveNormalBox_mono {a b : ℝ} (hab : a ≤ b) :
    positiveNormalBox a ⊆ positiveNormalBox b := by
  exact Set.prod_mono (Ioo_subset_Ioo_right hab) (Ioo_subset_Ioo_right hab)

theorem volume_real_positiveNormalBox {a : ℝ} (ha : 0 ≤ a) :
    volume.real (positiveNormalBox a) = a ^ 2 := by
  rw [positiveNormalBox, Measure.volume_eq_prod ℝ ℝ, Measure.real,
    Measure.prod_prod, ENNReal.toReal_mul]
  simp [Real.volume_Ioo, ENNReal.toReal_ofReal ha, pow_two]

/-- An absolute estimate on the actual difference of the two integrals.
No product factorization of the integrand is assumed. -/
theorem norm_integral_sub_positiveNormalBox_le
    {F : ℝ × ℝ → ℂ} {t₀ T a h B : ℝ}
    (ht₀ : 0 < t₀) (_hT : 0 < T) (hTt : T ≤ t₀)
    (ha : 0 ≤ a) (hh : 0 < h) (hB : 0 ≤ B)
    (hF : IntegrableOn F (positiveNormalBox t₀))
    (hbound : ∀ q ∈ positiveNormalBox t₀,
      ‖F q‖ ≤ B * q.1 ^ 2 * q.2 ^ 2 * Real.exp (-a * (q.1 + q.2) / h)) :
    ‖(∫ q in positiveNormalBox t₀, F q) -
      (∫ q in positiveNormalBox T, F q)‖ ≤
      B * t₀ ^ 6 * Real.exp (-a * T / h) := by
  let S := positiveNormalBox t₀ \ positiveNormalBox T
  have hsub : positiveNormalBox T ⊆ positiveNormalBox t₀ := positiveNormalBox_mono hTt
  rw [← setIntegral_diff (measurableSet_positiveNormalBox T) hF hsub]
  have hcompact : IsCompact (Icc (0 : ℝ) t₀ ×ˢ Icc (0 : ℝ) t₀) :=
    isCompact_Icc.prod isCompact_Icc
  have hSsub : S ⊆ Icc (0 : ℝ) t₀ ×ˢ Icc (0 : ℝ) t₀ :=
    diff_subset.trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hfinite : volume S < ⊤ := (measure_mono hSsub).trans_lt hcompact.measure_lt_top
  have hpoint (q : ℝ × ℝ) (hq : q ∈ S) :
      ‖F q‖ ≤ B * t₀ ^ 4 * Real.exp (-a * T / h) := by
    have hq₁ : 0 < q.1 ∧ q.1 < t₀ := hq.1.1
    have hq₂ : 0 < q.2 ∧ q.2 < t₀ := hq.1.2
    have hsum : T ≤ q.1 + q.2 := by
      by_contra hn
      apply hq.2
      exact ⟨⟨hq₁.1, by linarith⟩, ⟨hq₂.1, by linarith⟩⟩
    have hp₁ : q.1 ^ 2 ≤ t₀ ^ 2 := pow_le_pow_left₀ hq₁.1.le hq₁.2.le 2
    have hp₂ : q.2 ^ 2 ≤ t₀ ^ 2 := pow_le_pow_left₀ hq₂.1.le hq₂.2.le 2
    have he : Real.exp (-a * (q.1 + q.2) / h) ≤ Real.exp (-a * T / h) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hh.le
      exact mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr ha)
    calc
      _ ≤ B * q.1 ^ 2 * q.2 ^ 2 * Real.exp (-a * (q.1 + q.2) / h) := hbound q hq.1
      _ ≤ B * t₀ ^ 2 * t₀ ^ 2 * Real.exp (-a * T / h) := by gcongr
      _ = _ := by ring
  have hvol : volume.real S ≤ t₀ ^ 2 := by
    rw [← volume_real_positiveNormalBox ht₀.le]
    exact measureReal_mono diff_subset (by
      exact (measure_mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)).trans_lt
        hcompact.measure_lt_top |>.ne)
  calc
    _ ≤ (B * t₀ ^ 4 * Real.exp (-a * T / h)) * volume.real S :=
      norm_setIntegral_le_of_norm_le_const hfinite hpoint
    _ ≤ (B * t₀ ^ 4 * Real.exp (-a * T / h)) * t₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = _ := by ring

/-- The threshold is chosen before the amplitude and the integrand. Both
complex saddle factors are included, and any fixed inverse power is allowed. -/
theorem eventually_normalized_positiveNormalBox_truncation
    {β k tStar t₀ a : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (ht₀ : 0 < t₀)
    (ha : 0 < a) (hc : c ≠ 0) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ B : ℝ, 0 ≤ B → ∀ F : ℝ × ℝ → ℂ,
      IntegrableOn F (positiveNormalBox t₀) →
      (∀ q ∈ positiveNormalBox t₀,
        ‖F q‖ ≤ B * (h ^ N)⁻¹ * q.1 ^ 2 * q.2 ^ 2 *
          Real.exp (-a * (q.1 + q.2) / h)) →
      ‖logFlatSaddleNormalizer β k tStar c h ^ 2 *
        ((∫ q in positiveNormalBox t₀, F q) -
          (∫ q in positiveNormalBox (logFlatActiveWindow tStar h), F q))‖ ≤ ε * B := by
  have hlim := (tendsto_logFlatSaddleProduct_normalized_polynomial_stretched_error
    (k := k) hβ ht hc hc (mul_pos ha ht) (by norm_num : (0 : ℝ) < 1 / 4) N).const_mul
      (t₀ ^ 6)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hε),
    (tendsto_logFlatActiveWindow tStar).eventually (gt_mem_nhds ht₀),
    self_mem_nhdsWithin] with h hsmall hwindow hh
  intro B hB F hF hbound
  have hhpos : 0 < h := hh
  have hb := norm_integral_sub_positiveNormalBox_le ht₀
    (logFlatActiveWindow_pos ht h) hwindow.le ha.le hhpos
    (mul_nonneg hB (inv_nonneg.mpr (pow_nonneg hhpos.le N))) hF hbound
  have he : -a * logFlatActiveWindow tStar h / h =
      -(a * tStar) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)) := by
    calc
      _ = -a * (logFlatActiveWindow tStar h / h) := by ring
      _ = _ := by rw [logFlatActiveWindow_div tStar hhpos]; ring
  rw [norm_mul, pow_two]
  calc
    _ ≤ ‖logFlatSaddleNormalizer β k tStar c h * logFlatSaddleNormalizer β k tStar c h‖ *
        (B * (h ^ N)⁻¹ * t₀ ^ 6 * Real.exp (-a * logFlatActiveWindow tStar h / h)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = (t₀ ^ 6 *
        (‖logFlatSaddleNormalizer β k tStar c h * logFlatSaddleNormalizer β k tStar c h‖ *
          (h ^ N)⁻¹ * Real.exp (-(a * tStar) *
            Real.exp ((1 / 4 : ℝ) * Real.log (1 / h))))) * B := by rw [he]; ring
    _ ≤ ε * B := mul_le_mul_of_nonneg_right hsmall.le hB

end InfiniteZero
