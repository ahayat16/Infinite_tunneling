import InfiniteZero.ComplexLogFlatAsymptotic
import InfiniteZero.ComplexLogFlatCutoff

/-! The complex normal asymptotic with the actual potential's cutoff. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

def logFlatSaddleNormalizer (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℂ :=
  (Real.sqrt (logFlatSaddleRoot β k tStar c h).re : ℂ) *
    Complex.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
      (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)))

theorem tendsto_cutoff_complexLogFlatIntegral_normalized
    {β tStar t₀ t₂ M : ℝ} {c : ℂ} {χ : ℝ → ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₂ : 0 < t₂) (ht₂₀ : t₂ < t₀)
    (hc : 0 < c.re) (hχ : Continuous χ)
    (hbound : ∀ t ∈ Ioo 0 t₀, |χ t| ≤ M) (hone : ∀ t ∈ Ioo 0 t₂, χ t = 1) (m : ℕ) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer β (m : ℝ) tStar c h *
      (∫ t in Ioo 0 t₀, (χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t)) (𝓝[>] 0)
        (𝓝 ((tStar : ℂ) ^ (m + 1) * ((Real.sqrt (Real.pi / β) : ℝ) : ℂ))) := by
  let r : ℝ → ℂ := fun h =>
    (∫ t in Ioo 0 t₀, (χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t) -
      ∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t
  have hr : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖r h‖ ≤ (M * t₀ ^ m * (t₀ - t₂)) * Real.exp (-(c.re * t₂) / h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa only [neg_mul] using norm_cutoff_complexLogFlatIntegral_sub_le
      hβ hStar ht₂ ht₂₀ hh hc hχ hbound hone m
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  have herr := tendsto_logFlatSaddle_normalized_remainder (k := (m : ℝ))
    hβ hStar hcne (mul_pos hc ht₂) hr
  have hlim := (tendsto_complexLogFlatIntegral_normalized hβ hStar ht₂ hc m).add herr
  simp only [add_zero] at hlim
  apply hlim.congr
  intro h
  dsimp only [r, logFlatSaddleNormalizer]
  ring

/-- The cutoff in the constructed potential satisfies all hypotheses of the
proved complex normal asymptotic. This does not estimate the atomic source. -/
theorem CuspParameters.tendsto_normalCutoffIntegral_normalized {p : CuspParameters}
    (hp : p.BasicConditions) {c : ℂ} (hc : 0 < c.re) (m : ℕ) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer p.β (m : ℝ) p.tStar c h *
      (∫ t in Ioo 0 p.t₀, (p.χa t : ℂ) * complexLogFlatIntegrand p.β p.tStar h c m t))
        (𝓝[>] 0) (𝓝 ((p.tStar : ℂ) ^ (m + 1) * ((Real.sqrt (Real.pi / p.β) : ℝ) : ℂ))) := by
  obtain ⟨t₂, ht₂, ht₂₀, hone⟩ := hp.χa_one
  exact tendsto_cutoff_complexLogFlatIntegral_normalized hp.β_pos
    (hp.t₀_pos.trans hp.t₀_lt) ht₂ ht₂₀ hc hp.χa_smooth.continuous
    (M := 1) (fun t _ => by rw [abs_of_nonneg (hp.χa_range t).1]; exact (hp.χa_range t).2)
    (fun t ht => hone t ⟨ht.1.le, ht.2.le⟩) m

theorem CuspParameters.eventually_normalCutoffIntegral_ne_zero {p : CuspParameters}
    (hp : p.BasicConditions) {c : ℂ} (hc : 0 < c.re) (m : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Ioo 0 p.t₀, (p.χa t : ℂ) * complexLogFlatIntegrand p.β p.tStar h c m t) ≠ 0 := by
  have ht : 0 < p.tStar := hp.t₀_pos.trans hp.t₀_lt
  have hnonzero : (p.tStar : ℂ) ^ (m + 1) * ((Real.sqrt (Real.pi / p.β) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne'))
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hp.β_pos)).ne')
  filter_upwards [(CuspParameters.tendsto_normalCutoffIntegral_normalized hp hc m).eventually_ne hnonzero]
    with h hh
  intro he
  exact hh (by rw [he, mul_zero])

end InfiniteZero
