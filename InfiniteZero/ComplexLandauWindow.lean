import InfiniteZero.LogFlatActiveWindow

/-! The active radius window is smaller than the Gaussian proper-time scale. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero

theorem tendsto_logFlatActiveWindow_div_sqrt (tStar : ℝ) :
    Tendsto (fun h : ℝ => logFlatActiveWindow tStar h / Real.sqrt h)
      (𝓝[>] 0) (𝓝 0) := by
  have hs := (Real.continuous_sqrt.tendsto 0).comp (tendsto_logFlatActiveWindow_sq_div tStar)
  simp only [Real.sqrt_zero] at hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs,
    div_pow, Real.sq_sqrt hhpos.le]
  rfl

theorem tendsto_complex_div_sqrt_of_activeWindow
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {δ : ι → ℂ} {tStar M : ℝ}
    (hh : Tendsto h l (𝓝[>] 0))
    (hδ : ∀ᶠ i in l, ‖δ i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => δ i / (Real.sqrt (h i) : ℂ)) l (𝓝 0) := by
  have hlim : Tendsto (fun i => M * (logFlatActiveWindow tStar (h i) / Real.sqrt (h i)))
      l (𝓝 0) := by
    simpa using ((tendsto_logFlatActiveWindow_div_sqrt tStar).comp hh).const_mul M
  apply squeeze_zero_norm' (a := fun i => M *
    (logFlatActiveWindow tStar (h i) / Real.sqrt (h i))) ?_ hlim
  filter_upwards [hδ, hh.eventually self_mem_nhdsWithin] with i hi hhi
  have hp : 0 < h i := hhi
  have hs : 0 < Real.sqrt (h i) := Real.sqrt_pos.mpr hp
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc
    _ ≤ (M * logFlatActiveWindow tStar (h i)) / Real.sqrt (h i) :=
      div_le_div_of_nonneg_right hi hs.le
    _ = _ := by ring

end InfiniteZero
