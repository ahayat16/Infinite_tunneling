import InfiniteZero.LogFlatSmooth
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Smooth zero extension across a quadratic cusp

The stable family consists of a polynomially weighted log-flat normal factor
times a smooth compactly supported tangential factor evaluated at `u / t²`.
The first derivative stays in the span of this family. Induction then proves
smoothness, including the entire line `t = 0`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology ContDiff

namespace InfiniteZero

def cuspKernel (β tStar : ℝ) (k : ℕ) (P : Polynomial ℝ) (g : ℝ → ℝ)
    (z : ℝ × ℝ) : ℝ :=
  weightedLogFlat β tStar k P z.1 * g (z.2 / z.1 ^ 2)

@[simp] theorem cuspKernel_zero_fst (β tStar : ℝ) (k : ℕ) (P : Polynomial ℝ)
    (g : ℝ → ℝ) (u : ℝ) : cuspKernel β tStar k P g (0, u) = 0 := by
  simp [cuspKernel]

def cuspKernelDerivative (β tStar : ℝ) (k : ℕ) (P : Polynomial ℝ) (g : ℝ → ℝ)
    (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (cuspKernel β tStar (k + 1) (nextLogFlatPolynomial β k P) g z -
    2 * z.2 * cuspKernel β tStar (k + 3) P (deriv g) z) •
      ContinuousLinearMap.fst ℝ ℝ ℝ +
  cuspKernel β tStar (k + 2) P (deriv g) z • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem cuspKernel_isLittleO_norm_pow {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (k : ℕ) (P : Polynomial ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (u : ℝ) (N : ℕ) :
    cuspKernel β tStar k P g =o[𝓝 (0, u)]
      (fun z : ℝ × ℝ => ‖z - (0, u)‖ ^ N) := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hb : cuspKernel β tStar k P g =O[𝓝 (0, u)]
      (fun z : ℝ × ℝ => weightedLogFlat β tStar k P z.1) := by
    apply IsBigO.of_bound C
    apply Eventually.of_forall
    intro z
    dsimp [cuspKernel]
    rw [abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
  have hs : (fun z : ℝ × ℝ => weightedLogFlat β tStar k P z.1) =o[𝓝 (0, u)]
      (fun z : ℝ × ℝ => z.1 ^ N) := by
    simpa only [Function.comp_def] using
      (weightedLogFlat_isLittleO_pow hβ hStar k P N).comp_tendsto
        (continuous_fst.continuousAt.tendsto (x := (0, u)))
  have hp : (fun z : ℝ × ℝ => z.1 ^ N) =O[𝓝 (0, u)]
      (fun z : ℝ × ℝ => ‖z - (0, u)‖ ^ N) := by
    apply IsBigO.of_bound 1
    apply Eventually.of_forall
    intro z
    simp only [one_mul, norm_pow, Real.norm_eq_abs, abs_norm]
    apply pow_le_pow_left₀ (abs_nonneg _)
    have hf := norm_fst_le (z - (0, u))
    change ‖z.1 - (0 : ℝ)‖ ≤ ‖z - (0, u)‖ at hf
    simpa only [sub_zero, Real.norm_eq_abs] using hf
  exact (hb.trans_isLittleO hs).trans_isBigO hp

theorem hasFDerivAt_cuspKernel_zero_fst {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (k : ℕ) (P : Polynomial ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (u : ℝ) :
    HasFDerivAt (cuspKernel β tStar k P g) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0, u) := by
  rw [hasFDerivAt_iff_isLittleO]
  have hf : cuspKernel β tStar k P g =o[𝓝 (0, u)]
      (fun z : ℝ × ℝ => ‖z - (0, u)‖) := by
    simpa only [pow_one] using cuspKernel_isLittleO_norm_pow hβ hStar k P hg hgc u 1
  simpa only [cuspKernel_zero_fst, sub_zero, ContinuousLinearMap.zero_apply] using hf.of_norm_right

theorem hasFDerivAt_cuspKernel_of_fst_ne_zero {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (k : ℕ) (P : Polynomial ℝ)
    {g : ℝ → ℝ} (hg : Differentiable ℝ g) {z : ℝ × ℝ} (ht : z.1 ≠ 0) :
    HasFDerivAt (cuspKernel β tStar k P g) (cuspKernelDerivative β tStar k P g z) z := by
  have hw := (hasDerivAt_weightedLogFlat hβ hStar k P z.1).comp_hasFDerivAt z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hr := (((hasDerivAt_id z.1).pow 2).inv (pow_ne_zero 2 ht)).comp_hasFDerivAt z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hq := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).mul hr
  have hgg := (hg (z.2 * (z.1 ^ 2)⁻¹)).hasDerivAt.comp_hasFDerivAt z hq
  have hh := hw.mul hgg
  change HasFDerivAt (cuspKernel β tStar k P g) _ z at hh
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [cuspKernelDerivative, cuspKernel, weightedLogFlat, Function.comp_def,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    smul_eq_mul, div_eq_mul_inv, pow_add]
  field_simp
  ring

theorem hasFDerivAt_cuspKernel {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (k : ℕ) (P : Polynomial ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (z : ℝ × ℝ) :
    HasFDerivAt (cuspKernel β tStar k P g) (cuspKernelDerivative β tStar k P g z) z := by
  by_cases ht : z.1 = 0
  · rcases z with ⟨t, u⟩
    dsimp only at ht
    subst t
    simpa [cuspKernelDerivative] using hasFDerivAt_cuspKernel_zero_fst hβ hStar k P hg.continuous hgc u
  · exact hasFDerivAt_cuspKernel_of_fst_ne_zero hβ hStar k P
      (contDiff_infty_iff_deriv.mp hg).1 ht

theorem contDiff_cuspKernel_nat {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (n k : ℕ) (P : Polynomial ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : ContDiff ℝ n (cuspKernel β tStar k P g) := by
  induction n generalizing k P g with
  | zero =>
      apply contDiff_zero.mpr
      exact (show Differentiable ℝ (cuspKernel β tStar k P g) from
        fun z => (hasFDerivAt_cuspKernel hβ hStar k P hg hgc z).differentiableAt).continuous
  | succ n ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨cuspKernelDerivative β tStar k P g, ?_, hasFDerivAt_cuspKernel hβ hStar k P hg hgc⟩
      have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
      have h1 := ih (k + 1) (nextLogFlatPolynomial β k P) hg hgc
      have h2 := ih (k + 2) P hgd hgc.deriv
      have h3 := ih (k + 3) P hgd hgc.deriv
      exact ((h1.sub ((contDiff_const.mul contDiff_snd).mul h3)).smul contDiff_const).add
        (h2.smul contDiff_const)

/-- A smooth compact tangential cutoff preserves full smoothness through the
singular quadratic rescaling, because the normal factor is log-flat. -/
theorem contDiff_cuspKernel {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (k : ℕ) (P : Polynomial ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : ContDiff ℝ ∞ (cuspKernel β tStar k P g) := by
  rw [contDiff_infty]
  exact fun n => contDiff_cuspKernel_nat hβ hStar n k P hg hgc

end InfiniteZero
