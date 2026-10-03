import InfiniteZero.ComplexLandauEffectiveRadius
import InfiniteZero.BridgeActionTaylor

/-! Comparison of the real action at the effective radius with the real
part of the linearized complex action. This controls normalized complex
proper-time tails without estimating the divergent coth near time zero. -/

noncomputable section
open Set

namespace InfiniteZero

theorem abs_bridgeAction_effectiveRadius_sub_linear_le {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) {δ : ℂ} (hδ : ‖δ‖ ≤ r / 4) :
    |bridgeAction b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) -
      bridgeAction b E r - deriv (bridgeAction b E) r * δ.re| ≤
      (b + deriv (bridgeAction b E) r * (2 / r)) * ‖δ‖ ^ 2 := by
  let ρ := complexLandauEffectiveRadius ((r : ℂ) + δ)
  have hq := abs_complexLandauEffectiveRadius_sub_linear_le hr hδ
  have hl := abs_complexLandauEffectiveRadius_sub_le hr hδ
  have hj := deriv_bridgeAction_pos hb.ne' hE r
  have hsq : (ρ - r) ^ 2 ≤ (2 * ‖δ‖) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hl 2
  calc
    _ = |(bridgeAction b E ρ - bridgeAction b E r -
      deriv (bridgeAction b E) r * (ρ - r)) +
      deriv (bridgeAction b E) r * (ρ - r - δ.re)| := by congr 1; ring
    _ ≤ |bridgeAction b E ρ - bridgeAction b E r -
      deriv (bridgeAction b E) r * (ρ - r)| +
      |deriv (bridgeAction b E) r * (ρ - r - δ.re)| := abs_add_le _ _
    _ ≤ b / 4 * (ρ - r) ^ 2 + deriv (bridgeAction b E) r * ((2 / r) * ‖δ‖ ^ 2) := by
      apply add_le_add (abs_bridgeAction_sub_linear_le hb hE r ρ)
      rw [abs_mul, abs_of_pos hj]
      exact mul_le_mul_of_nonneg_left hq hj.le
    _ ≤ b / 4 * (2 * ‖δ‖) ^ 2 + deriv (bridgeAction b E) r * ((2 / r) * ‖δ‖ ^ 2) := by
      gcongr
    _ = _ := by ring

def complexLandauActionErrorConstant (b Emax rMin rMax : ℝ) : ℝ :=
  b + deriv (bridgeAction b Emax) rMax * (2 / rMin)

theorem complexLandauActionErrorConstant_pos {b Emax rMin : ℝ}
    (hb : 0 < b) (hEmax : 0 < Emax) (hMin : 0 < rMin) (rMax : ℝ) :
    0 < complexLandauActionErrorConstant b Emax rMin rMax := by
  unfold complexLandauActionErrorConstant
  have := deriv_bridgeAction_pos hb.ne' hEmax rMax
  positivity

theorem abs_bridgeAction_effectiveRadius_sub_linear_uniform_le
    {b E Emax rMin rMax r : ℝ} (hb : 0 < b) (hE : 0 < E) (hEmax : E ≤ Emax)
    (hMin : 0 < rMin) (hr : r ∈ Icc rMin rMax) {δ : ℂ} (hδ : ‖δ‖ ≤ rMin / 4) :
    |bridgeAction b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) -
      bridgeAction b E r - deriv (bridgeAction b E) r * δ.re| ≤
      complexLandauActionErrorConstant b Emax rMin rMax * ‖δ‖ ^ 2 := by
  have hrpos := hMin.trans_le hr.1
  have hEM := hE.trans_le hEmax
  have hderiv : deriv (bridgeAction b E) r ≤ deriv (bridgeAction b Emax) rMax := by
    rw [deriv_bridgeAction hb.ne' hE, deriv_bridgeAction hb.ne' hEM]
    gcongr
    exact hr.2
  apply (abs_bridgeAction_effectiveRadius_sub_linear_le hb hE hrpos
    (hδ.trans (by linarith [hr.1]))).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  unfold complexLandauActionErrorConstant
  apply add_le_add le_rfl
  exact mul_le_mul hderiv (div_le_div_of_nonneg_left (by norm_num) hMin hr.1)
    (by positivity) (deriv_bridgeAction_pos hb.ne' hEM rMax).le

theorem norm_complexLandau_normalizer_relative_le
    {b h E Emax rMin rMax r : ℝ} (hb : 0 < b) (hh : 0 < h)
    (hE : 0 < E) (hEmax : E ≤ Emax) (hMin : 0 < rMin)
    (hr : r ∈ Icc rMin rMax) {δ : ℂ} (hδ : ‖δ‖ ≤ rMin / 4) :
    ‖Complex.exp (((bridgeAction b E r : ℝ) +
      ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ))‖ *
        Real.exp (-bridgeAction b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) / h) ≤
      Real.exp (complexLandauActionErrorConstant b Emax rMin rMax * ‖δ‖ ^ 2 / h) := by
  have hbound := abs_bridgeAction_effectiveRadius_sub_linear_uniform_le hb hE hEmax hMin hr hδ
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.div_ofReal_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  have he := (abs_le.mp hbound).1
  have hdiv := div_le_div_of_nonneg_right (by linarith :
    bridgeAction b E r + deriv (bridgeAction b E) r * δ.re -
      bridgeAction b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) ≤
        complexLandauActionErrorConstant b Emax rMin rMax * ‖δ‖ ^ 2) hh.le
  convert hdiv using 1
  ring

end InfiniteZero
