import InfiniteZero.ComplexLandauEffectiveRadius
import InfiniteZero.BridgeActionTaylor

/-!
# Effective radii and action on complex disks of semiclassical radius

The closed disk of radius `h ≤ min 1 (rMin/4)` around a real radius in
`[rMin,rMax]` stays inside the convergence domain of the complex Landau
kernel. Its effective real radius remains in one fixed positive annulus.
The change in the radial action is bounded by an explicit constant times
`h`, uniformly in the energy and the base radius on positive rectangles.
-/

noncomputable section
open Set

namespace InfiniteZero

/-- The effective radius actually moves by at most `2h`, stronger than the
`3h` estimate sufficient for the subsequent Cauchy bounds. -/
theorem complexLandau_smallDisk_bounds {rMin rMax r h : ℝ}
    (hMin : 0 < rMin) (hr : r ∈ Icc rMin rMax)
    (hh : h ∈ Ioc 0 (min 1 (rMin / 4))) {z : ℂ}
    (hz : ‖z - (r : ℂ)‖ ≤ h) :
    0 < (z ^ 2).re ∧
      complexLandauEffectiveRadius z ∈ Icc (rMin / 2) (rMax + 1) ∧
      |complexLandauEffectiveRadius z - r| ≤ 2 * h := by
  have hrpos : 0 < r := hMin.trans_le hr.1
  have hhsmall := le_min_iff.mp hh.2
  have hδ : ‖z - (r : ℂ)‖ ≤ r / 4 :=
    hz.trans (hhsmall.2.trans (by linarith [hr.1]))
  have heq : (r : ℂ) + (z - (r : ℂ)) = z := by ring
  have hpos := re_sq_ofReal_add_pos hrpos hδ
  have hb := complexLandauEffectiveRadius_bounds hrpos hδ
  have hdist := abs_complexLandauEffectiveRadius_sub_le hrpos hδ
  rw [heq] at hpos hb hdist
  exact ⟨hpos, ⟨by linarith [hb.1, hr.1], by linarith [hb.2, hr.2, hhsmall.1]⟩,
    hdist.trans (mul_le_mul_of_nonneg_left hz (by norm_num))⟩

/-- Explicit action cost on the small disk, with a constant independent of
the energy, real radius, semiclassical parameter and complex point. -/
theorem abs_bridgeAction_effectiveRadius_sub_le_smallDisk
    {b Emin Emax rMin rMax E r h : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hMin : 0 < rMin)
    (hE : E ∈ Icc Emin Emax) (hr : r ∈ Icc rMin rMax)
    (hh : h ∈ Ioc 0 (min 1 (rMin / 4))) {z : ℂ}
    (hz : ‖z - (r : ℂ)‖ ≤ h) :
    |bridgeAction b E (complexLandauEffectiveRadius z) - bridgeAction b E r| ≤
      (Real.sqrt (b ^ 2 * rMax ^ 2 + 4 * Emax) + b) * h := by
  have hEpos : 0 < E := hEmin.trans_le hE.1
  have hrpos : 0 < r := hMin.trans_le hr.1
  have hMax : 0 ≤ rMax := hrpos.le.trans hr.2
  have hh1 : h ≤ 1 := (le_min_iff.mp hh.2).1
  have hdist := (complexLandau_smallDisk_bounds hMin hr hh hz).2.2
  have hr2 : r ^ 2 ≤ rMax ^ 2 := (sq_le_sq₀ hrpos.le hMax).mpr hr.2
  have hrad : b ^ 2 * r ^ 2 + 4 * E ≤ b ^ 2 * rMax ^ 2 + 4 * Emax := by
    have hmul := mul_le_mul_of_nonneg_left hr2 (sq_nonneg b)
    linarith [hE.2]
  have hderiv : |deriv (bridgeAction b E) r| ≤
      Real.sqrt (b ^ 2 * rMax ^ 2 + 4 * Emax) / 2 := by
    rw [abs_of_pos (deriv_bridgeAction_pos hb.ne' hEpos r), deriv_bridgeAction hb.ne' hEpos]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad) (by norm_num)
  have hlinear : |deriv (bridgeAction b E) r * (complexLandauEffectiveRadius z - r)| ≤
      Real.sqrt (b ^ 2 * rMax ^ 2 + 4 * Emax) * h := by
    rw [abs_mul]
    calc
      _ ≤ (Real.sqrt (b ^ 2 * rMax ^ 2 + 4 * Emax) / 2) * (2 * h) :=
        mul_le_mul hderiv hdist (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsq : (complexLandauEffectiveRadius z - r) ^ 2 ≤ (2 * h) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hh.1.le)).mpr hdist
    simpa only [sq_abs] using hs
  have hh2 : h ^ 2 ≤ h := by nlinarith [hh.1]
  have hquadratic : b / 4 * (complexLandauEffectiveRadius z - r) ^ 2 ≤ b * h := by
    calc
      _ ≤ b / 4 * (2 * h) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = b * h ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh2 hb.le
  calc
    _ = |(bridgeAction b E (complexLandauEffectiveRadius z) - bridgeAction b E r -
          deriv (bridgeAction b E) r * (complexLandauEffectiveRadius z - r)) +
          deriv (bridgeAction b E) r * (complexLandauEffectiveRadius z - r)| := by
      congr 1
      ring
    _ ≤ |bridgeAction b E (complexLandauEffectiveRadius z) - bridgeAction b E r -
          deriv (bridgeAction b E) r * (complexLandauEffectiveRadius z - r)| +
          |deriv (bridgeAction b E) r * (complexLandauEffectiveRadius z - r)| :=
      abs_add_le _ _
    _ ≤ b * h + Real.sqrt (b ^ 2 * rMax ^ 2 + 4 * Emax) * h :=
      add_le_add ((abs_bridgeAction_sub_linear_le hb hEpos r
        (complexLandauEffectiveRadius z)).trans hquadratic) hlinear
    _ = _ := by ring

/-- A closed-ball package for Cauchy estimates. The radius threshold and
action constant are fixed before every parameter of the kernel evaluation. -/
theorem exists_complexLandau_smallDisk_action_bounds
    {b Emin Emax rMin rMax : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hMin : 0 < rMin) :
    ∃ h₀ > 0, ∃ C > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rMin rMax,
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z ∈ Metric.closedBall (r : ℂ) h,
        0 < (z ^ 2).re ∧
        complexLandauEffectiveRadius z ∈ Icc (rMin / 2) (rMax + 1) ∧
        |bridgeAction b E (complexLandauEffectiveRadius z) - bridgeAction b E r| ≤ C * h := by
  refine ⟨min 1 (rMin / 4), lt_min (by norm_num) (by positivity),
    Real.sqrt (b ^ 2 * rMax ^ 2 + 4 * Emax) + b,
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hb, ?_⟩
  intro E hE r hr h hh hsmall z hz
  have hz' : ‖z - (r : ℂ)‖ ≤ h := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hg := complexLandau_smallDisk_bounds hMin hr ⟨hh, hsmall⟩ hz'
  exact ⟨hg.1, hg.2.1,
    abs_bridgeAction_effectiveRadius_sub_le_smallDisk hb hEmin hMin hE hr ⟨hh, hsmall⟩ hz'⟩

end InfiniteZero
