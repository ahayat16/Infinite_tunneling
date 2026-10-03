import InfiniteZero.ComplexLogFlatErrors
import InfiniteZero.LogFlatActiveWindow

/-!
# Favorable connector bounds with a bounded multiplier

The sectorial real-part inequality retains the negative exponential rate
of the true saddle connector. A bounded multiplier costs only its bound,
not an exponential with the opposite sign. On the active window the
connector is negligible after the actual complex saddle normalization.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

theorem norm_integral_logFlatContourFunction_mul_connector_le
    {β k tStar h v a K : ℝ} {c : ℂ} {B : ℂ → ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hh : 0 < h) (hv : |v| ≤ Real.pi)
    (hc : 0 < c.re)
    (hrot : ∀ η ∈ uIcc 0 v, c.re ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re)
    (hK : 0 ≤ K)
    (hB : ∀ η ∈ uIcc 0 v, ‖B ((a : ℂ) + (η : ℂ) * Complex.I)‖ ≤ K) :
    ‖∫ η in (0 : ℝ)..v,
      logFlatContourFunction β k tStar c h ((a : ℂ) + (η : ℂ) * Complex.I) *
        B ((a : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      (Real.pi * logFlatErrorMajorant β k * K) *
        Real.exp (-logFlatContourErrorRate tStar c a / h) := by
  let A := logFlatErrorMajorant β k * Real.exp (-logFlatContourErrorRate tStar c a / h)
  have hA : 0 ≤ A := by dsimp [A, logFlatErrorMajorant]; positivity
  have hbound : ∀ η ∈ uIoc (0 : ℝ) v,
      ‖logFlatContourFunction β k tStar c h ((a : ℂ) + (η : ℂ) * Complex.I) *
        B ((a : ℂ) + (η : ℂ) * Complex.I)‖ ≤ A * K := by
    intro η hη
    have hη' := uIoc_subset_uIcc hη
    have hηabs : |η| ≤ Real.pi := by
      have hi : |η| ≤ |v| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hη'
      exact hi.trans hv
    have hg := norm_logFlatContourFunction_left_le hβ ht hh hηabs hc (hrot η hη') k
      (x := a) (y₂ := a) le_rfl
    have he : Real.exp (-(β / 2) * a ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg a]
    have hscalar : ‖logFlatContourFunction β k tStar c h
        ((a : ℂ) + (η : ℂ) * Complex.I)‖ ≤ A :=
      hg.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hA)
    rw [norm_mul]
    exact mul_le_mul hscalar (hB η hη') (norm_nonneg _) hA
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simp only [sub_zero] at hi
  calc
    _ ≤ (A * K) * |v| := hi
    _ ≤ (A * K) * Real.pi := mul_le_mul_of_nonneg_left hv (mul_nonneg hA hK)
    _ = _ := by dsimp [A]; ring

/-- The branch threshold is independent of the endpoint and of the bounded
multiplier. This applies to amplitudes depending on further parameters. -/
theorem eventually_forall_logFlatContourFunction_mul_connector_le
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a K : ℝ, 0 ≤ K → ∀ B : ℂ → ℂ,
      (∀ η ∈ uIcc 0 (logFlatSaddleRoot β k tStar c h).im,
        ‖B ((a : ℂ) + (η : ℂ) * Complex.I)‖ ≤ K) →
      ‖∫ η in (0 : ℝ)..(logFlatSaddleRoot β k tStar c h).im,
        logFlatContourFunction β k tStar c h ((a : ℂ) + (η : ℂ) * Complex.I) *
          B ((a : ℂ) + (η : ℂ) * Complex.I)‖ ≤
        (Real.pi * logFlatErrorMajorant β k * K) *
          Real.exp (-logFlatContourErrorRate tStar c a / h) := by
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  filter_upwards [eventually_logFlatSaddleRoot_connector_re (k := k) hβ ht hc,
    eventually_logFlatSaddleRoot_arg (k := k) hβ ht hcne, self_mem_nhdsWithin]
    with h hrot harg hh
  intro a K hK B hB
  exact norm_integral_logFlatContourFunction_mul_connector_le hβ ht hh
    (harg.2.2.trans (Complex.abs_arg_le_pi c)) hc hrot hK hB

theorem eventually_logFlatActive_multiplier_connector_le
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ K : ℝ, 0 ≤ K → ∀ B : ℂ → ℂ,
      (∀ η ∈ uIcc 0 (logFlatSaddleRoot β k tStar c h).im,
        ‖B ((logFlatActiveLogCut h : ℂ) + (η : ℂ) * Complex.I)‖ ≤ K) →
      ‖∫ η in (0 : ℝ)..(logFlatSaddleRoot β k tStar c h).im,
        logFlatContourFunction β k tStar c h
          ((logFlatActiveLogCut h : ℂ) + (η : ℂ) * Complex.I) *
        B ((logFlatActiveLogCut h : ℂ) + (η : ℂ) * Complex.I)‖ ≤
        (Real.pi * logFlatErrorMajorant β k * K) *
          Real.exp (-(tStar * c.re) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h))) := by
  filter_upwards [eventually_forall_logFlatContourFunction_mul_connector_le
    (k := k) hβ ht hc, self_mem_nhdsWithin] with h hh hpos
  intro K hK B hB
  have hb := hh (logFlatActiveLogCut h) K hK B hB
  simpa only [neg_div, logFlatActiveWindow_error_rate tStar c hpos, neg_mul] using hb

/-- An arbitrary scale-dependent bounded amplitude preserves the stretched
exponential gain. Integrability, when needed for contour identities, is a
separate property; the absolute Bochner-integral bound itself requires only
the displayed bound on the connector. -/
theorem tendsto_logFlatActive_multiplier_connector_normalized
    {β k tStar K : ℝ} {c : ℂ} {B : ℝ → ℂ → ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) (hK : 0 ≤ K)
    (hB : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ η ∈ uIcc 0 (logFlatSaddleRoot β k tStar c h).im,
        ‖B h ((logFlatActiveLogCut h : ℂ) + (η : ℂ) * Complex.I)‖ ≤ K) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer β k tStar c h *
      (∫ η in (0 : ℝ)..(logFlatSaddleRoot β k tStar c h).im,
        logFlatContourFunction β k tStar c h
          ((logFlatActiveLogCut h : ℂ) + (η : ℂ) * Complex.I) *
        B h ((logFlatActiveLogCut h : ℂ) + (η : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 0) := by
  have hcne : c ≠ 0 := by intro he; simp [he] at hc
  apply tendsto_logFlatSaddle_normalized_stretched_remainder hβ ht hcne
    (mul_pos ht hc) (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [eventually_logFlatActive_multiplier_connector_le (k := k) hβ ht hc,
    hB] with h hh hBh
  exact hh K hK (B h) hBh

end InfiniteZero
