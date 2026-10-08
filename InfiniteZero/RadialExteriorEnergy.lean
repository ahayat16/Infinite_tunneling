import InfiniteZero.RadialCaccioppoli
import InfiniteZero.RadialExteriorCutoffs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Finite exterior derivative energy follows from the radial equation and
radial L² alone. Compact Caccioppoli estimates and expanding intervals prove
integrability without assuming decay of derivatives. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace InfiniteZero

theorem IsRadialODESolutionOn.integrableOn_radial_deriv_sq
    {a : ℝ} {q f df : ℝ → ℝ} (hf : IsRadialODESolutionOn q f df a)
    (ha : 0 < a) (hq : ContinuousOn q (Ioi a)) (hq0 : ∀ r ∈ Ioi a, 0 ≤ q r)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi a)) :
    IntegrableOn (fun r => r * df r ^ 2) (Ioi (a + 2)) := by
  have hfc : ContinuousOn f (Ioi a) := fun r hr =>
    (hf.deriv r hr).continuousAt.continuousWithinAt
  have hdfc : ContinuousOn df (Ioi a) := fun r hr =>
    (hf.second r hr).continuousAt.continuousWithinAt
  have henergyc : ContinuousOn (fun r => r * df r ^ 2) (Ioi a) :=
    continuousOn_id.mul (hdfc.pow 2)
  have hmassc : ContinuousOn (fun r => r * f r ^ 2) (Ioi a) :=
    continuousOn_id.mul (hfc.pow 2)
  obtain ⟨D, hD, hderiv⟩ := exists_radialExteriorCutoff_deriv_bound a
  let J := ∫ r in Ioi a, r * f r ^ 2
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (4 * D ^ 2 * J) (a + 2) (l := atTop) (b := fun n : ℕ => a + (n : ℝ) + 2)
  · intro n
    exact ((henergyc.mono (by intro r hr; exact lt_of_lt_of_le (by linarith) hr.1)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  · exact tendsto_atTop_add_const_right _ 2
      (tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop)
  · apply Eventually.of_forall
    intro n
    let χ := radialExteriorCutoff a n
    have hl : a < a + 1 := by linarith
    have hlu : a + 1 ≤ a + (n : ℝ) + 3 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hbase : a + 2 ≤ a + (n : ℝ) + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hsubset : Icc (a + 1) (a + (n : ℝ) + 3) ⊆ Ioi a := by
      intro r hr
      exact hl.trans_le hr.1
    have hχc : Continuous χ := (radialExteriorCutoff_contDiff a n).continuous
    have hdχc : Continuous (_root_.deriv χ) := continuous_deriv_radialExteriorCutoff a n
    have hχd : ∀ r ∈ Icc (a + 1) (a + (n : ℝ) + 3),
        HasDerivAt χ (_root_.deriv χ r) r := by
      intro r _
      exact ((radialExteriorCutoff_contDiff a n).differentiable (by simp) r).hasDerivAt
    have hcc := radial_caccioppoli ha hf hl hlu (hq.mono hsubset)
      (fun r hr => hq0 r (hsubset hr)) hχd hdχc.continuousOn
      (radialExteriorCutoff_zero_left a n le_rfl)
      (radialExteriorCutoff_zero_right a n le_rfl)
    have hχenergy : ContinuousOn (fun r => r * χ r ^ 2 * df r ^ 2)
        (Icc (a + 1) (a + (n : ℝ) + 3)) :=
      (continuousOn_id.mul (hχc.continuousOn.pow 2)).mul ((hdfc.mono hsubset).pow 2)
    have hχmass : ContinuousOn (fun r => r * _root_.deriv χ r ^ 2 * f r ^ 2)
        (Icc (a + 1) (a + (n : ℝ) + 3)) :=
      (continuousOn_id.mul (hdχc.continuousOn.pow 2)).mul ((hfc.mono hsubset).pow 2)
    have hmassint : IntervalIntegrable (fun r => r * f r ^ 2) volume
        (a + 1) (a + (n : ℝ) + 3) :=
      (hmassc.mono hsubset).intervalIntegrable_of_Icc hlu
    have hmassbound : (∫ r in (a + 1)..(a + (n : ℝ) + 3), r * f r ^ 2) ≤ J := by
      rw [intervalIntegral.integral_of_le hlu]
      apply setIntegral_mono_set hfi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact mul_nonneg (ha.trans hr).le (sq_nonneg _)
      · exact Eventually.of_forall (fun r hr => hsubset (Ioc_subset_Icc_self hr))
    have hχmassbound : (∫ r in (a + 1)..(a + (n : ℝ) + 3),
        r * _root_.deriv χ r ^ 2 * f r ^ 2) ≤ D ^ 2 * J := by
      calc
        _ ≤ ∫ r in (a + 1)..(a + (n : ℝ) + 3), D ^ 2 * (r * f r ^ 2) := by
          apply intervalIntegral.integral_mono_on hlu
            (hχmass.intervalIntegrable_of_Icc hlu) (hmassint.const_mul _)
          intro r hr
          have hs : _root_.deriv χ r ^ 2 ≤ D ^ 2 := by
            have hs := (sq_le_sq₀ (abs_nonneg _) hD.le).mpr (hderiv n r)
            simpa only [sq_abs] using hs
          have h := mul_le_mul_of_nonneg_right hs
            (mul_nonneg (ha.trans (hsubset hr)).le (sq_nonneg (f r)))
          nlinarith only [h]
        _ ≤ D ^ 2 * J := by
          rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left hmassbound (sq_nonneg D)
    have hrestriction : (∫ r in (a + 2)..(a + (n : ℝ) + 2), r * df r ^ 2) ≤
        ∫ r in (a + 1)..(a + (n : ℝ) + 3), r * χ r ^ 2 * df r ^ 2 := by
      calc
        _ = ∫ r in (a + 2)..(a + (n : ℝ) + 2), r * χ r ^ 2 * df r ^ 2 := by
          apply intervalIntegral.integral_congr
          intro r hr
          rw [uIcc_of_le hbase] at hr
          dsimp only
          rw [show χ r = 1 from radialExteriorCutoff_one a n hr.1 hr.2, one_pow, mul_one]
        _ ≤ _ := by
          apply intervalIntegral.integral_mono_interval (by linarith) hbase (by linarith)
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
            exact mul_nonneg
              (mul_nonneg (ha.trans (hsubset (Ioc_subset_Icc_self hr))).le (sq_nonneg _))
              (sq_nonneg _)
          · exact hχenergy.intervalIntegrable_of_Icc hlu
    have hnorm : (∫ r in (a + 2)..(a + (n : ℝ) + 2), ‖r * df r ^ 2‖) =
        ∫ r in (a + 2)..(a + (n : ℝ) + 2), r * df r ^ 2 := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hbase] at hr
      exact Real.norm_of_nonneg (mul_nonneg (by linarith [hr.1]) (sq_nonneg _))
    rw [hnorm]
    calc
      _ ≤ _ := hrestriction
      _ ≤ _ := hcc
      _ ≤ 4 * (D ^ 2 * J) := mul_le_mul_of_nonneg_left hχmassbound (by norm_num)
      _ = _ := by ring

end InfiniteZero
