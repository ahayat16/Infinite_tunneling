import InfiniteZero.ComplexLogFlatPhaseGrowth
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Comparing the two scalar saddle sizes

The real Gaussian scale uses Re w, while the complex Hessian uses 1+w.
For the same saddle their squared sizes have ratio ‖1+w‖ / Re w, which
tends to one. No statement identifies normalizations of different states.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

/-- A bounded imaginary part gives an elementary quantitative comparison. -/
theorem norm_one_add_div_re_bounds {w : ℂ} {M : ℝ}
    (hr : 0 < w.re) (him : |w.im| ≤ M) :
    1 ≤ ‖1 + w‖ / w.re ∧ ‖1 + w‖ / w.re ≤ 1 + (1 + M) / w.re := by
  have hr' : 0 ≤ 1 + w.re := by linarith
  have hlo : 1 + w.re ≤ ‖1 + w‖ := by
    simpa only [Complex.add_re, Complex.one_re] using Complex.re_le_norm (1 + w)
  have hup : ‖1 + w‖ ≤ 1 + w.re + M := by
    have hn := Complex.norm_le_abs_re_add_abs_im (1 + w)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      zero_add, abs_of_nonneg hr'] at hn
    linarith
  constructor
  · exact (le_div_iff₀ hr).mpr (by linarith)
  · apply (div_le_iff₀ hr).mpr
    calc
      _ ≤ 1 + w.re + M := hup
      _ = (1 + (1 + M) / w.re) * w.re := by field_simp; ring

/-- The Hessian-to-real-Gaussian squared-size ratio tends to one, with all
scalar parameters fixed before h tends to zero. -/
theorem tendsto_norm_one_add_logFlatSaddleRoot_div_re
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    Tendsto (fun h : ℝ => ‖1 + logFlatSaddleRoot β k tStar c h‖ /
      (logFlatSaddleRoot β k tStar c h).re) (𝓝[>] 0) (𝓝 1) := by
  have hre := tendsto_re_logFlatSaddleRoot (k := k) hβ.ne' ht.ne' hc
  let M := ‖logFlatLambertDisplacement β k tStar c‖ + Real.pi
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] 0,
      1 ≤ ‖1 + logFlatSaddleRoot β k tStar c h‖ /
        (logFlatSaddleRoot β k tStar c h).re ∧
      ‖1 + logFlatSaddleRoot β k tStar c h‖ /
        (logFlatSaddleRoot β k tStar c h).re ≤
          1 + (1 + M) / (logFlatSaddleRoot β k tStar c h).re := by
    filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc]
      with h hw
    exact norm_one_add_div_re_bounds (by linarith [hw.1]) hw.2.2.2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun h : ℝ => 1 + (1 + M) /
      (logFlatSaddleRoot β k tStar c h).re) (𝓝[>] 0) (𝓝 1) by
      simpa only [add_zero] using (hre.const_div_atTop (1 + M)).const_add 1)
    (hbound.mono fun _ hh => hh.1) (hbound.mono fun _ hh => hh.2)

theorem eventually_norm_one_add_logFlatSaddleRoot_div_re_bounds
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      1 ≤ ‖1 + logFlatSaddleRoot β k tStar c h‖ /
        (logFlatSaddleRoot β k tStar c h).re ∧
      ‖1 + logFlatSaddleRoot β k tStar c h‖ /
        (logFlatSaddleRoot β k tStar c h).re ≤ 2 := by
  have hupper := (tendsto_norm_one_add_logFlatSaddleRoot_div_re
    (k := k) hβ ht hc).eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc,
    hupper] with h hw hu
  exact ⟨(norm_one_add_div_re_bounds (by linarith [hw.1]) hw.2.2.2).1, hu.le⟩

/-- Positive size of the complex-Hessian leading term used in the manuscript. -/
def logFlatSaddleTexSize (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℝ :=
  tStar ^ (k + 1) * Real.sqrt (Real.pi /
    (β * ‖1 + logFlatSaddleRoot β k tStar c h‖)) *
      Real.exp (-(logFlatSaddleValue β k tStar c h).re)

/-- The manuscript's complex Gaussian prefactor, with the principal square root. -/
def logFlatSaddleTexLeading (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℂ :=
  ((tStar ^ (k + 1) : ℝ) : ℂ) *
    Complex.sqrt ((Real.pi : ℂ) / ((β : ℂ) * (1 + logFlatSaddleRoot β k tStar c h))) *
      Complex.exp (-logFlatSaddleValue β k tStar c h)

private theorem norm_complex_sqrt (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
  simpa [Complex.sqrt, Real.sqrt_eq_rpow, one_div] using Complex.norm_cpow_inv_nat z 2

theorem norm_logFlatSaddleTexLeading {β k tStar h : ℝ} (c : ℂ)
    (hβ : 0 < β) (ht : 0 < tStar) :
    ‖logFlatSaddleTexLeading β k tStar c h‖ = logFlatSaddleTexSize β k tStar c h := by
  have hp : 0 < tStar ^ (k + 1) := Real.rpow_pos_of_pos ht _
  simp only [logFlatSaddleTexLeading, logFlatSaddleTexSize, norm_mul, norm_complex_sqrt,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
    abs_of_pos Real.pi_pos, abs_of_pos hβ, Complex.norm_exp, Complex.neg_re]

theorem logFlatSaddleLeadingSize_sq_div_texSize_sq
    {β k tStar h : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hr : 0 < (logFlatSaddleRoot β k tStar c h).re) :
    logFlatSaddleLeadingSize β k tStar c h ^ 2 /
      logFlatSaddleTexSize β k tStar c h ^ 2 =
        ‖1 + logFlatSaddleRoot β k tStar c h‖ /
          (logFlatSaddleRoot β k tStar c h).re := by
  have hz : 0 < ‖1 + logFlatSaddleRoot β k tStar c h‖ := by
    have hb := Complex.re_le_norm (1 + logFlatSaddleRoot β k tStar c h)
    simp only [Complex.add_re, Complex.one_re] at hb
    linarith
  have hp : 0 < tStar ^ (k + 1) := Real.rpow_pos_of_pos ht _
  have he : 0 < Real.exp (-(logFlatSaddleValue β k tStar c h).re) := Real.exp_pos _
  simp only [logFlatSaddleLeadingSize, logFlatSaddleTexSize, mul_pow,
    Real.sq_sqrt (div_pos Real.pi_pos (mul_pos hβ hr)).le,
    Real.sq_sqrt (div_pos Real.pi_pos (mul_pos hβ hz)).le]
  field_simp [hp.ne', he.ne', hβ.ne', hr.ne', hz.ne', Real.pi_ne_zero]

theorem tendsto_logFlatSaddleLeadingSize_sq_div_texSize_sq
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    Tendsto (fun h : ℝ => logFlatSaddleLeadingSize β k tStar c h ^ 2 /
      logFlatSaddleTexSize β k tStar c h ^ 2) (𝓝[>] 0) (𝓝 1) := by
  apply (tendsto_norm_one_add_logFlatSaddleRoot_div_re (k := k) hβ ht hc).congr'
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc]
    with h hw
  exact (logFlatSaddleLeadingSize_sq_div_texSize_sq hβ ht (by linarith [hw.1])).symm

/-- A direct two-sided comparison, convenient when multiplying both sizes
by the same positive physical prefactor. -/
theorem eventually_logFlatSaddleLeadingSize_sq_bounds
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      0 < logFlatSaddleTexSize β k tStar c h ∧
      logFlatSaddleTexSize β k tStar c h ^ 2 ≤
        logFlatSaddleLeadingSize β k tStar c h ^ 2 ∧
      logFlatSaddleLeadingSize β k tStar c h ^ 2 ≤
        2 * logFlatSaddleTexSize β k tStar c h ^ 2 := by
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc,
    eventually_norm_one_add_logFlatSaddleRoot_div_re_bounds (k := k) hβ ht hc]
    with h hw hb
  have hr : 0 < (logFlatSaddleRoot β k tStar c h).re := by linarith [hw.1]
  have hz : 0 < ‖1 + logFlatSaddleRoot β k tStar c h‖ := by
    have hh := Complex.re_le_norm (1 + logFlatSaddleRoot β k tStar c h)
    simp only [Complex.add_re, Complex.one_re] at hh
    linarith
  have hs : 0 < logFlatSaddleTexSize β k tStar c h := by
    unfold logFlatSaddleTexSize
    positivity
  rw [← logFlatSaddleLeadingSize_sq_div_texSize_sq hβ ht hr] at hb
  refine ⟨hs, ?_, ?_⟩
  · simpa only [one_mul] using (le_div_iff₀ (sq_pos_of_pos hs)).mp hb.1
  · exact (div_le_iff₀ (sq_pos_of_pos hs)).mp hb.2

end InfiniteZero
