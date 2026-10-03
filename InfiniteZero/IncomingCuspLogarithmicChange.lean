import InfiniteZero.IncomingCuspDensityNormalization
import InfiniteZero.LogFlatMultiplierChange
import InfiniteZero.NormalBoxTruncation
import InfiniteZero.CuspActiveWindow

/-!
# Exact logarithmic form of the truncated physical incoming density

Fubini uses absolute integrability of the actual density. The real cutoff
equals one on the chosen window before the logarithmic changes are made.
The two Jacobians give the factor `tStar^6`; no analytic continuation of a
smooth cutoff is used. Core and full energies remain distinct throughout.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem incomingCuspDensity_logarithmic_change
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ec Ef s r T : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ec) (hEf : 0 < Ef)
    (hs : |s| ≤ p.s₀) (hr : |r| ≤ p.s₀) (hT : 0 < T) (hTt : T ≤ p.t₀)
    (hcut : ∀ t ∈ Icc 0 T, p.χa t = 1) :
    p.incomingCuspNormalization L h Ec Ef *
      (∫ q in positiveNormalBox T, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) =
      ((p.χb s * p.χb r : ℝ) : ℂ) * (p.tStar : ℂ) ^ 6 *
        (∫ x in Ioi (Real.log (p.tStar / T)), ∫ y in Ioi (Real.log (p.tStar / T)),
          logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h (x : ℂ) *
          logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h (y : ℂ) *
          p.frozenCuspKernelPhaseProfile L h Ec Ef s r
            ((p.tStar : ℂ) * Complex.exp (-(x : ℂ)))
            ((p.tStar : ℂ) * Complex.exp (-(y : ℂ)))) := by
  let f := complexLogFlatIntegrand p.β p.tStar h (p.activeSaddleSlope L) 2
  let B : ℝ → ℝ → ℂ := fun t u =>
    p.frozenCuspKernelPhaseProfile L h Ec Ef s r (t : ℂ) (u : ℂ)
  let K : ℂ := ((p.χb s * p.χb r : ℝ) : ℂ)
  have hi := (integrableOn_incomingCuspDensity_normals hp hL hh hEc hEf
    (abs_le.mp hs) (abs_le.mp hr)).mono_set (positiveNormalBox_mono hTt)
  have hfub : (∫ q in positiveNormalBox T,
      p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) =
      ∫ t in Ioo 0 T, ∫ u in Ioo 0 T, p.incomingCuspDensity L h Ec Ef t u s r := by
    rw [positiveNormalBox, Measure.volume_eq_prod ℝ ℝ]
    exact setIntegral_prod _ (by simpa only [Measure.volume_eq_prod ℝ ℝ] using hi)
  calc
    _ = ∫ t in Ioo 0 T, ∫ u in Ioo 0 T,
        p.incomingCuspNormalization L h Ec Ef * p.incomingCuspDensity L h Ec Ef t u s r := by
      rw [hfub]
      simp only [integral_const_mul]
    _ = ∫ t in Ioo 0 T, ∫ u in Ioo 0 T, K * (f t * f u * B t u) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      change p.incomingCuspNormalization L h Ec Ef * p.incomingCuspDensity L h Ec Ef t u s r =
        K * (f t * f u * B t u)
      rw [incomingCuspNormalization_mul_density p L h Ec Ef s r ht.1 hu.1,
        hcut t ⟨ht.1.le, ht.2.le⟩, hcut u ⟨hu.1.le, hu.2.le⟩]
      dsimp [K, f, B]
      simp only [one_mul]
      ring
    _ = K * (∫ t in Ioo 0 T, ∫ u in Ioo 0 T, f t * f u * B t u) := by
      simp only [integral_const_mul]
    _ = _ := by
      rw [integral_complexLogFlat_product_multiplier_logarithmic_change
        (hp.t₀_pos.trans hp.t₀_lt) hT]
      simp only [B, K, logFlatContourFunction, Complex.ofReal_mul, Complex.ofReal_exp,
        Complex.ofReal_neg, Nat.cast_ofNat, show 2 * (2 + 1) = 6 by norm_num]
      ring

theorem eventually_incomingCuspDensity_active_logarithmic_change
    {p : CuspParameters} (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ Ec > 0, ∀ Ef > 0,
      ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      p.incomingCuspNormalization L h Ec Ef *
        (∫ q in positiveNormalBox (logFlatActiveWindow p.tStar h),
          p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) =
        ((p.χb s * p.χb r : ℝ) : ℂ) * (p.tStar : ℂ) ^ 6 *
          (∫ x in Ioi (logFlatActiveLogCut h), ∫ y in Ioi (logFlatActiveLogCut h),
            logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h (x : ℂ) *
            logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h (y : ℂ) *
            p.frozenCuspKernelPhaseProfile L h Ec Ef s r
              ((p.tStar : ℂ) * Complex.exp (-(x : ℂ)))
              ((p.tStar : ℂ) * Complex.exp (-(y : ℂ)))) := by
  filter_upwards [eventually_activeWindow_local hp hL, self_mem_nhdsWithin] with h hw hh
  intro Ec hEc Ef hEf s r hs hr
  simpa only [logFlatActiveWindow_log_ratio (hp.t₀_pos.trans hp.t₀_lt) h] using
    incomingCuspDensity_logarithmic_change hp hL hh hEc hEf hs hr hw.1.1 hw.1.2.le hw.2.1

end InfiniteZero.CuspParameters
