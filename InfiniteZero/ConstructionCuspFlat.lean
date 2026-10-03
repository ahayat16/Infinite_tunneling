import InfiniteZero.ConstructionCuspSmoothAway
import InfiniteZero.LogFlat

/-!
# Value flatness and the first derivative at the cusp tip

The cutoff factors are uniformly bounded. The normal coordinate is bounded by
the Euclidean distance to the tip, so the scalar log-flat decay implies decay
of the cusp value faster than every power of that distance.

Value flatness alone does not imply smoothness of all derivatives. This file
proves continuity and a zero first derivative; higher derivative control is a
separate obligation.
-/

noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace InfiniteZero.CuspParameters

@[simp] theorem normalCoordinate_cuspTip (p : CuspParameters) :
    p.normalCoordinate p.cuspTip = 0 := by
  simp [normalCoordinate, cuspTip]

@[simp] theorem cuspPlus_cuspTip (p : CuspParameters) : p.cuspPlus p.cuspTip = 0 := by
  simp [cuspPlus]

/-- The normal coordinate is the orthogonal projection of the displacement
from the tip onto the unit outgoing normal. -/
theorem normalCoordinate_eq_inner (p : CuspParameters) (x : Plane) :
    p.normalCoordinate x = inner ℝ (x - p.cuspTip) cuspNormal := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    cuspNormal, normalCoordinate, cuspTip, Matrix.vecHead, Matrix.vecTail]
  ring

theorem abs_normalCoordinate_le_norm_sub_tip (p : CuspParameters) (x : Plane) :
    |p.normalCoordinate x| ≤ ‖x - p.cuspTip‖ := by
  rw [normalCoordinate_eq_inner]
  simpa only [norm_cuspNormal, mul_one] using
    abs_real_inner_le_norm (x - p.cuspTip) cuspNormal

theorem abs_cuspPlus_le_logFlat {p : CuspParameters} (h : p.BasicConditions) (x : Plane) :
    |p.cuspPlus x| ≤ p.a * logFlat p.β p.tStar (p.normalCoordinate x) := by
  by_cases ht : 0 < p.normalCoordinate x
  · rw [cuspPlus_eq_formula_of_normal_pos h ht, logFlat_of_pos _ _ ht]
    have ha := h.χa_range (p.normalCoordinate x)
    have hb := h.χb_range (p.tangentCoordinate x / p.normalCoordinate x ^ 2)
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos h.a_pos,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg ha.1, abs_of_nonneg hb.1]
    have he : 0 ≤ p.a * Real.exp (-p.β * (Real.log (p.tStar / p.normalCoordinate x)) ^ 2) :=
      mul_nonneg h.a_pos.le (Real.exp_pos _).le
    have hab : p.χa (p.normalCoordinate x) *
        p.χb (p.tangentCoordinate x / p.normalCoordinate x ^ 2) ≤ 1 :=
      mul_le_one₀ ha.2 hb.1 hb.2
    nlinarith [mul_le_mul_of_nonneg_left hab he]
  · simp [cuspPlus, logFlat, ht]

theorem cuspPlus_isBigO_logFlat {p : CuspParameters} (h : p.BasicConditions) :
    p.cuspPlus =O[𝓝 p.cuspTip] (fun x => logFlat p.β p.tStar (p.normalCoordinate x)) := by
  apply IsBigO.of_bound p.a
  apply Eventually.of_forall
  intro x
  calc
    ‖p.cuspPlus x‖ = |p.cuspPlus x| := Real.norm_eq_abs _
    _ ≤ p.a * logFlat p.β p.tStar (p.normalCoordinate x) := abs_cuspPlus_le_logFlat h x
    _ ≤ p.a * ‖logFlat p.β p.tStar (p.normalCoordinate x)‖ :=
      mul_le_mul_of_nonneg_left (le_abs_self _) h.a_pos.le

/-- At the tip the cusp value vanishes faster than every Euclidean distance
power. This estimate includes approaches from outside the cusp. -/
theorem cuspPlus_isLittleO_norm_pow {p : CuspParameters} (h : p.BasicConditions) (N : ℕ) :
    p.cuspPlus =o[𝓝 p.cuspTip] (fun x => ‖x - p.cuspTip‖ ^ N) := by
  have hn : Tendsto p.normalCoordinate (𝓝 p.cuspTip) (𝓝 0) := by
    simpa only [normalCoordinate_cuspTip] using
      (normalCoordinate_contDiff p).continuous.continuousAt.tendsto (x := p.cuspTip)
  have hscalar := logFlat_isLittleO_pow h.β_pos (lt_trans h.t₀_pos h.t₀_lt) N
  have hcomp : (fun x => logFlat p.β p.tStar (p.normalCoordinate x)) =o[𝓝 p.cuspTip]
      (fun x => p.normalCoordinate x ^ N) := by
    simpa only [Function.comp_def] using hscalar.comp_tendsto hn
  have hnorm : (fun x => p.normalCoordinate x ^ N) =O[𝓝 p.cuspTip]
      (fun x => ‖x - p.cuspTip‖ ^ N) := by
    apply IsBigO.of_bound 1
    apply Eventually.of_forall
    intro x
    simp only [one_mul, norm_pow, Real.norm_eq_abs, abs_norm]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_normalCoordinate_le_norm_sub_tip p x) N
  exact ((cuspPlus_isBigO_logFlat h).trans_isLittleO hcomp).trans_isBigO hnorm

theorem cuspPlus_hasFDerivAt_tip {p : CuspParameters} (h : p.BasicConditions) :
    HasFDerivAt p.cuspPlus (0 : Plane →L[ℝ] ℝ) p.cuspTip := by
  rw [hasFDerivAt_iff_isLittleO]
  have hf : p.cuspPlus =o[𝓝 p.cuspTip] (fun x => ‖x - p.cuspTip‖) := by
    simpa only [pow_one] using cuspPlus_isLittleO_norm_pow h 1
  simpa only [cuspPlus_cuspTip, sub_zero, ContinuousLinearMap.zero_apply] using hf.of_norm_right

theorem cuspPlus_continuousAt_tip {p : CuspParameters} (h : p.BasicConditions) :
    ContinuousAt p.cuspPlus p.cuspTip :=
  (cuspPlus_hasFDerivAt_tip h).continuousAt

/-- The zero extension is continuous everywhere, including the unique tip. -/
theorem cuspPlus_continuous {p : CuspParameters} (h : p.BasicConditions) :
    Continuous p.cuspPlus := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = p.cuspTip
  · simpa only [hx] using cuspPlus_continuousAt_tip h
  · exact (cuspPlus_contDiffAt_of_ne_tip h hx).continuousAt

theorem cuspMinus_continuous {p : CuspParameters} (h : p.BasicConditions) :
    Continuous p.cuspMinus :=
  (cuspPlus_continuous h).comp reflection_contDiff.continuous

end InfiniteZero.CuspParameters
