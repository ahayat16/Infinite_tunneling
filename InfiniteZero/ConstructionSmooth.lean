import InfiniteZero.ConstructionCoreSmooth
import InfiniteZero.ConstructionCuspFormula
import InfiniteZero.ConstructionCuspFlat
import InfiniteZero.ConstructionNonradial
import InfiniteZero.CuspKernelSmooth
import InfiniteZero.CompactSmoothDerivatives

/-!
# Smoothness and admissibility of the explicit cusp potential

The log-flat kernel absorbs the singular quadratic tangential rescaling.
Together with the global cutoff formula and the smooth radial core, this
proves admissibility from the elementary parameter conditions alone.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero.CuspParameters

theorem cuspPlus_contDiff {p : CuspParameters} (h : p.BasicConditions) :
    ContDiff ℝ ∞ p.cuspPlus := by
  have hk := contDiff_cuspKernel h.β_pos (lt_trans h.t₀_pos h.t₀_lt) 0
    (1 : Polynomial ℝ) h.χb_smooth h.χb_support
  have hcoords : ContDiff ℝ ∞ (fun x : Plane => (p.normalCoordinate x, p.tangentCoordinate x)) :=
    (normalCoordinate_contDiff p).prodMk (tangentCoordinate_contDiff p)
  have hf := ((contDiff_const (c := -p.a)).mul
    (h.χa_smooth.comp (normalCoordinate_contDiff p))).mul
    (hk.comp hcoords)
  convert hf using 1
  funext x
  simpa only [Function.comp_apply, cuspKernel, weightedLogFlat, pow_zero, inv_one,
    Polynomial.eval_one, mul_one, one_mul] using cuspPlus_eq_logFlat_formula h x

theorem cuspMinus_contDiff_of_tip {p : CuspParameters} (h : p.BasicConditions)
    (htip : ContDiffAt ℝ ∞ p.cuspPlus p.cuspTip) :
    ContDiff ℝ ∞ p.cuspMinus :=
  ((cuspPlus_contDiff_iff_tip h).mpr htip).comp reflection_contDiff

theorem potential_contDiff_of_tip {p : CuspParameters} (h : p.BasicConditions)
    (htip : ContDiffAt ℝ ∞ p.cuspPlus p.cuspTip) :
    ContDiff ℝ ∞ p.potential :=
  (core_contDiff h.r₀_pos).add
    (contDiff_const.mul (((cuspPlus_contDiff_iff_tip h).mpr htip).add
      (cuspMinus_contDiff_of_tip h htip)))

theorem admissiblePotential_of_tip {p : CuspParameters} (h : p.BasicConditions)
    (htip : ContDiffAt ℝ ∞ p.cuspPlus p.cuspTip) : AdmissiblePotential p.potential where
  smooth := potential_contDiff_of_tip h htip
  compactSupport := potential_hasCompactSupport h
  range := potential_range h
  nonradial := potential_nonradial h

theorem cuspMinus_contDiff {p : CuspParameters} (h : p.BasicConditions) :
    ContDiff ℝ ∞ p.cuspMinus :=
  (cuspPlus_contDiff h).comp reflection_contDiff

theorem potential_contDiff {p : CuspParameters} (h : p.BasicConditions) :
    ContDiff ℝ ∞ p.potential :=
  potential_contDiff_of_tip h (cuspPlus_contDiff h).contDiffAt

/-- All admissibility requirements are now proved, with no analytic admission. -/
theorem admissiblePotential {p : CuspParameters} (h : p.BasicConditions) :
    AdmissiblePotential p.potential :=
  admissiblePotential_of_tip h (cuspPlus_contDiff h).contDiffAt

end InfiniteZero.CuspParameters
