import InfiniteZero.ComplexLambertRoot

/-!
# Uniform asymptotics of the large complex Lambert branch

For a bounded complex displacement `d`, the input `L = ℓ + d` lies in the
contraction regime once the real parameter `ℓ` is sufficiently large.
The canonical branch then satisfies `w = L - log L + O(log ℓ / ℓ)`,
uniformly in `d`. No special-function existence or asymptotic is assumed.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

/-- A logarithm estimate on a bounded perturbation of the positive real axis. -/
theorem norm_complex_log_real_add_le {ℓ M : ℝ} {d : ℂ}
    (hℓ : 0 < ℓ) (hM : 2 * M ≤ ℓ) (hd : ‖d‖ ≤ M) :
    ‖Complex.log ((ℓ : ℂ) + d)‖ ≤ |Real.log ℓ| + 1 := by
  have hdre : -M ≤ d.re := by
    have := (neg_le_abs d.re).trans ((Complex.abs_re_le_norm d).trans hd)
    linarith
  have hhalf : 0 < ℓ / 2 := by positivity
  have hL : ℓ / 2 ≤ ((ℓ : ℂ) + d).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hb := norm_complex_log_sub_le_of_re_ge hhalf hL
    (show ℓ / 2 ≤ (ℓ : ℂ).re by simp; linarith)
  simp only [add_sub_cancel_left] at hb
  have hdiff : ‖Complex.log ((ℓ : ℂ) + d) - Complex.log (ℓ : ℂ)‖ ≤ 1 := by
    apply hb.trans
    calc
      (ℓ / 2)⁻¹ * ‖d‖ ≤ (ℓ / 2)⁻¹ * (ℓ / 2) := by
        gcongr
        linarith
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hhalf)
  have ht := norm_add_le (Complex.log ((ℓ : ℂ) + d) - Complex.log (ℓ : ℂ))
    (Complex.log (ℓ : ℂ))
  rw [sub_add_cancel, ← Complex.ofReal_log hℓ.le, Complex.norm_real,
    Real.norm_eq_abs] at ht
  rw [← Complex.ofReal_log hℓ.le] at hdiff
  linarith

/-- Explicit finite inequalities suffice for all the uniform branch estimates. -/
theorem largeLambertRoot_real_add_estimates {ℓ M : ℝ} {d : ℂ}
    (hℓ : 4 ≤ ℓ) (hM : 4 * M ≤ ℓ) (hloglo : 1 ≤ Real.log ℓ)
    (hloghi : 16 * Real.log ℓ ≤ ℓ) (hd : ‖d‖ ≤ M) :
    2 ≤ (largeLambertRoot ((ℓ : ℂ) + d)).re ∧
    ℓ / 2 ≤ (largeLambertRoot ((ℓ : ℂ) + d)).re ∧
    largeLambertRoot ((ℓ : ℂ) + d) +
      Complex.log (largeLambertRoot ((ℓ : ℂ) + d)) = (ℓ : ℂ) + d ∧
    largeLambertRoot ((ℓ : ℂ) + d) *
      Complex.exp (largeLambertRoot ((ℓ : ℂ) + d)) = Complex.exp ((ℓ : ℂ) + d) ∧
    ‖largeLambertRoot ((ℓ : ℂ) + d) -
      (((ℓ : ℂ) + d) - Complex.log ((ℓ : ℂ) + d))‖ ≤ 8 * Real.log ℓ / ℓ ∧
    |(largeLambertRoot ((ℓ : ℂ) + d)).im| ≤ M + Real.pi ∧
    ‖largeLambertRoot ((ℓ : ℂ) + d) - ((ℓ : ℂ) + d)‖ ≤ 4 * Real.log ℓ := by
  have hℓpos : 0 < ℓ := by linarith
  have hdre : -M ≤ d.re := by
    have := (neg_le_abs d.re).trans ((Complex.abs_re_le_norm d).trans hd)
    linarith
  have hlognonneg : 0 ≤ Real.log ℓ := by linarith
  have hR : 0 ≤ 4 * Real.log ℓ := by positivity
  have hden : ℓ / 2 ≤ ((ℓ : ℂ) + d).re - 4 * Real.log ℓ := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hL : 4 * Real.log ℓ + 2 ≤ ((ℓ : ℂ) + d).re := by linarith
  have hlog : ‖Complex.log ((ℓ : ℂ) + d)‖ ≤ (4 * Real.log ℓ) / 2 := by
    have hb := norm_complex_log_real_add_le hℓpos (show 2 * M ≤ ℓ by linarith) hd
    rw [abs_of_nonneg hlognonneg] at hb
    linarith
  obtain ⟨hdisc, hre, he, hexp, herr⟩ := largeLambertRoot_estimates hR hL hlog
  refine ⟨hre, ?_, he, hexp, ?_, ?_, ?_⟩
  · exact hden.trans (re_ge_of_mem_lambert_disc hdisc)
  · apply herr.trans
    calc
      4 * Real.log ℓ / (((ℓ : ℂ) + d).re - 4 * Real.log ℓ)
          ≤ 4 * Real.log ℓ / (ℓ / 2) :=
        div_le_div_of_nonneg_left hR (by positivity) hden
      _ = 8 * Real.log ℓ / ℓ := by ring
  · have him := large_complex_lambert_im_bound he
    simp only [Complex.add_im, Complex.ofReal_im, zero_add] at him
    exact him.trans (add_le_add ((Complex.abs_im_le_norm d).trans hd) le_rfl)
  · simpa only [Metric.mem_closedBall, dist_eq_norm] using hdisc

/-- A single threshold works for every displacement in a fixed closed ball. -/
theorem eventually_largeLambertRoot_real_add_estimates (M : ℝ) :
    ∀ᶠ ℓ : ℝ in atTop, ∀ d : ℂ, ‖d‖ ≤ M →
      2 ≤ (largeLambertRoot ((ℓ : ℂ) + d)).re ∧
      ℓ / 2 ≤ (largeLambertRoot ((ℓ : ℂ) + d)).re ∧
      largeLambertRoot ((ℓ : ℂ) + d) +
        Complex.log (largeLambertRoot ((ℓ : ℂ) + d)) = (ℓ : ℂ) + d ∧
      largeLambertRoot ((ℓ : ℂ) + d) *
        Complex.exp (largeLambertRoot ((ℓ : ℂ) + d)) = Complex.exp ((ℓ : ℂ) + d) ∧
      ‖largeLambertRoot ((ℓ : ℂ) + d) -
        (((ℓ : ℂ) + d) - Complex.log ((ℓ : ℂ) + d))‖ ≤ 8 * Real.log ℓ / ℓ ∧
      |(largeLambertRoot ((ℓ : ℂ) + d)).im| ≤ M + Real.pi ∧
      ‖largeLambertRoot ((ℓ : ℂ) + d) - ((ℓ : ℂ) + d)‖ ≤ 4 * Real.log ℓ := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16)
  have hlarge : ∀ᶠ ℓ : ℝ in atTop, 1 ≤ Real.log ℓ :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (4 * M),
    hlarge, hsmall] with ℓ hℓ hM hloglo hloghi
  have hℓpos : 0 ≤ ℓ := by linarith
  have hlogpos : 0 ≤ Real.log ℓ := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hℓpos,
    abs_of_nonneg hlogpos] at hloghi
  intro d hd
  exact largeLambertRoot_real_add_estimates hℓ hM hloglo (by linarith) hd

/-- The logarithm itself changes by at most `2 M / ℓ`. -/
theorem norm_complex_log_real_add_sub_log_le {ℓ M : ℝ} {d : ℂ}
    (hℓ : 0 < ℓ) (hM : 2 * M ≤ ℓ) (hd : ‖d‖ ≤ M) :
    ‖Complex.log ((ℓ : ℂ) + d) - (Real.log ℓ : ℂ)‖ ≤ 2 * M / ℓ := by
  have hdre : -M ≤ d.re := by
    have := (neg_le_abs d.re).trans ((Complex.abs_re_le_norm d).trans hd)
    linarith
  have hL : ℓ / 2 ≤ ((ℓ : ℂ) + d).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hb := norm_complex_log_sub_le_of_re_ge (show 0 < ℓ / 2 by positivity) hL
    (show ℓ / 2 ≤ (ℓ : ℂ).re by simp; linarith)
  rw [← Complex.ofReal_log hℓ.le, add_sub_cancel_left] at hb
  apply hb.trans
  calc
    (ℓ / 2)⁻¹ * ‖d‖ ≤ (ℓ / 2)⁻¹ * M := by gcongr
    _ = 2 * M / ℓ := by ring

/-- The form with the real logarithm makes the bounded displacement explicit. -/
theorem eventually_norm_largeLambertRoot_sub_real_log_le (M : ℝ) :
    ∀ᶠ ℓ : ℝ in atTop, ∀ d : ℂ, ‖d‖ ≤ M →
      ‖largeLambertRoot ((ℓ : ℂ) + d) - (((ℓ - Real.log ℓ : ℝ) : ℂ) + d)‖ ≤
        (8 * Real.log ℓ + 2 * M) / ℓ := by
  filter_upwards [eventually_largeLambertRoot_real_add_estimates M,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (2 * M)] with ℓ hmain hℓ hM
  intro d hd
  have hb := (hmain d hd).2.2.2.2.1
  have hl := norm_complex_log_real_add_sub_log_le hℓ hM hd
  have he : largeLambertRoot ((ℓ : ℂ) + d) - (((ℓ - Real.log ℓ : ℝ) : ℂ) + d) =
      (largeLambertRoot ((ℓ : ℂ) + d) -
        (((ℓ : ℂ) + d) - Complex.log ((ℓ : ℂ) + d))) -
      (Complex.log ((ℓ : ℂ) + d) - (Real.log ℓ : ℂ)) := by
    push_cast
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ 8 * Real.log ℓ / ℓ + 2 * M / ℓ := add_le_add hb hl
    _ = (8 * Real.log ℓ + 2 * M) / ℓ := by ring

/-- The complex-logarithm expansion has a remainder tending uniformly to zero. -/
theorem tendstoUniformlyOn_largeLambertRoot_remainder (M : ℝ) :
    TendstoUniformlyOn
      (fun ℓ : ℝ => fun d : ℂ => largeLambertRoot ((ℓ : ℂ) + d) -
        (((ℓ : ℂ) + d) - Complex.log ((ℓ : ℂ) + d)))
      (fun _ => 0) atTop (Metric.closedBall 0 M) := by
  have ht : Tendsto (fun ℓ : ℝ => 8 * Real.log ℓ / ℓ) atTop (𝓝 0) := by
    simpa only [id_eq, mul_zero, mul_div_assoc] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul 8
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_largeLambertRoot_real_add_estimates M,
    ht.eventually (gt_mem_nhds hε)] with ℓ hmain hεℓ
  intro d hd
  have hd' : ‖d‖ ≤ M := by simpa only [Metric.mem_closedBall, dist_zero_right] using hd
  simpa only [dist_zero_left] using ((hmain d hd').2.2.2.2.1.trans_lt hεℓ)

/-- Uniformly on bounded displacements, `w = ℓ - log ℓ + d + o(1)`. -/
theorem tendstoUniformlyOn_largeLambertRoot_real_log_remainder (M : ℝ) :
    TendstoUniformlyOn
      (fun ℓ : ℝ => fun d : ℂ => largeLambertRoot ((ℓ : ℂ) + d) -
        (((ℓ - Real.log ℓ : ℝ) : ℂ) + d))
      (fun _ => 0) atTop (Metric.closedBall 0 M) := by
  have ht₁ : Tendsto (fun ℓ : ℝ => 8 * Real.log ℓ / ℓ) atTop (𝓝 0) := by
    simpa only [id_eq, mul_zero, mul_div_assoc] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul 8
  have ht₂ : Tendsto (fun ℓ : ℝ => 2 * M / ℓ) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (2 * M)
  have ht : Tendsto (fun ℓ : ℝ => (8 * Real.log ℓ + 2 * M) / ℓ) atTop (𝓝 0) := by
    simpa only [add_zero, add_div] using ht₁.add ht₂
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_norm_largeLambertRoot_sub_real_log_le M,
    ht.eventually (gt_mem_nhds hε)] with ℓ hmain hεℓ
  intro d hd
  have hd' : ‖d‖ ≤ M := by simpa only [Metric.mem_closedBall, dist_zero_right] using hd
  simpa only [dist_zero_left] using (hmain d hd').trans_lt hεℓ

end InfiniteZero
