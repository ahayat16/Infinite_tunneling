import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Uniform absorption of the weighted overlap and true atomic residual. -/

namespace InfiniteZero
open Filter
open scoped Topology

/-- All constants precede the coupling. An exponentially small overlap
defect and a residual of size `λ exp(-d λ)` consume at most half the
available rank-one coercivity, uniformly over smaller actual errors. -/
theorem exists_weighted_residual_absorption {γ C c K d : ℝ}
    (hγ : 0 < γ) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 ≤ K) (hd : 0 < d) :
    ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling →
      C * Real.exp (-c * coupling) ≤ 1 ∧
      ∀ δ r m : ℝ, 0 ≤ δ → 0 ≤ m →
        δ ≤ C * Real.exp (-c * coupling) →
        r ≤ K * coupling * Real.exp (-d * coupling) →
        m ≤ 1 + C * Real.exp (-c * coupling) →
        γ / 4 * coupling + 2 * (γ * coupling) * δ ^ 2 + r * m ≤
          γ / 2 * coupling := by
  have hec : Tendsto (fun x : ℝ => Real.exp (-c * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hed : Tendsto (fun x : ℝ => Real.exp (-d * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hd))
  have hδlim : Tendsto (fun x : ℝ => C * Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hec.const_mul C
  have hrlim : Tendsto (fun x : ℝ => K * Real.exp (-d * x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hed.const_mul K
  have hsum : Tendsto (fun x : ℝ =>
      2 * γ * (C * Real.exp (-c * x)) ^ 2 +
        K * Real.exp (-d * x) * (1 + C * Real.exp (-c * x))) atTop (𝓝 0) := by
    simpa using ((hδlim.pow 2).const_mul (2 * γ)).add
      (hrlim.mul (hδlim.const_add 1))
  have hevent : ∀ᶠ x : ℝ in atTop,
      C * Real.exp (-c * x) ≤ 1 ∧
      2 * γ * (C * Real.exp (-c * x)) ^ 2 +
        K * Real.exp (-d * x) * (1 + C * Real.exp (-c * x)) ≤ γ / 4 := by
    filter_upwards [hδlim.eventually_le_const (by norm_num : (0 : ℝ) < 1),
      hsum.eventually_le_const (show (0 : ℝ) < γ / 4 from
        div_pos hγ (by norm_num))] with x h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro coupling hcoupling
  have hcN : N ≤ coupling := (le_max_left _ _).trans hcoupling
  have hc0 : 0 ≤ coupling := zero_le_one.trans ((le_max_right _ _).trans hcoupling)
  refine ⟨(hN coupling hcN).1, ?_⟩
  intro δ r m hδ0 hm0 hδ hr hm
  have hδ2 := (sq_le_sq₀ hδ0 (mul_nonneg hC (Real.exp_pos _).le)).mpr hδ
  have hδbound := mul_le_mul_of_nonneg_left hδ2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hγ.le hc0))
  have hrbound := mul_le_mul hr hm hm0
    (mul_nonneg (mul_nonneg hK hc0) (Real.exp_pos _).le)
  have hbudget := mul_le_mul_of_nonneg_right (hN coupling hcN).2 hc0
  nlinarith only [hδbound, hrbound, hbudget]

end InfiniteZero
