import InfiniteZero.CuspKernelSmooth
import InfiniteZero.CompactSmoothDerivatives
import InfiniteZero.LogFlatDerivativeLoss
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Quantitative derivative closure of the quadratic cusp family

Rewriting the normal derivative with the compact profile `s * g' s`
keeps every derivative in a finite sum of the same log-flat family.
The jet recurrence has constants independent of the tangential coordinate.
Every fixed jet is bounded by any strictly weaker log-flat profile, uniformly
on a compact normal interval, including the zero extension. All constants
precede both coordinates; there is no semiclassical parameter in these bounds.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

/-- The additional tangential profile in the normal derivative. -/
def cuspNormalProfile (g : ℝ → ℝ) (s : ℝ) : ℝ := s * deriv g s

theorem contDiff_cuspNormalProfile {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cuspNormalProfile g) :=
  contDiff_id.mul (contDiff_infty_iff_deriv.mp hg).2

theorem hasCompactSupport_cuspNormalProfile {g : ℝ → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (cuspNormalProfile g) :=
  hg.deriv.mul_left

/-- Absorb the explicit tangential coordinate into a compact profile. -/
theorem cuspKernel_normalProfile (β tStar : ℝ) (k : ℕ) (P : Polynomial ℝ)
    (g : ℝ → ℝ) (z : ℝ × ℝ) :
    z.2 * cuspKernel β tStar (k + 3) P (deriv g) z =
      cuspKernel β tStar (k + 1) P (cuspNormalProfile g) z := by
  by_cases ht : z.1 = 0
  · simp [cuspKernel, weightedLogFlat, cuspNormalProfile, ht, logFlat]
  · simp only [cuspKernel, weightedLogFlat, cuspNormalProfile]
    simp only [pow_add, pow_one]
    field_simp

/-- The genuine derivative stays in the cusp family with no unbounded
coordinate multiplier outside its profiles. -/
theorem cuspKernel_fderiv_eq {β tStar : ℝ} (hβ : 0 < β) (hStar : 0 < tStar)
    (k : ℕ) (P : Polynomial ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    fderiv ℝ (cuspKernel β tStar k P g) = fun z =>
      (cuspKernel β tStar (k + 1) (nextLogFlatPolynomial β k P) g z -
        2 * cuspKernel β tStar (k + 1) P (cuspNormalProfile g) z) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
      cuspKernel β tStar (k + 2) P (deriv g) z •
          ContinuousLinearMap.snd ℝ ℝ ℝ := by
  funext z
  rw [(hasFDerivAt_cuspKernel hβ hStar k P hg hgc z).fderiv]
  unfold cuspKernelDerivative
  rw [mul_assoc, cuspKernel_normalProfile]

private theorem norm_iteratedFDeriv_smul_fixed {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (v : V) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => f y • v) z‖ =
      ‖iteratedFDeriv ℝ n f z‖ * ‖v‖ := by
  rw [iteratedFDeriv_smul_const_apply (contDiff_infty.mp hf n).contDiffAt]
  change ‖(iteratedFDeriv ℝ n f z).smulRight v‖ = _
  exact ContinuousMultilinearMap.norm_smulRight _ _

private theorem norm_iteratedFDeriv_frame_le
    {f₁ f₂ f₃ : (ℝ × ℝ) → ℝ} (h₁ : ContDiff ℝ ∞ f₁)
    (h₂ : ContDiff ℝ ∞ f₂) (h₃ : ContDiff ℝ ∞ f₃) (n : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun y =>
        (f₁ y - 2 * f₂ y) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        f₃ y • ContinuousLinearMap.snd ℝ ℝ ℝ) z‖ ≤
      ‖iteratedFDeriv ℝ n f₁ z‖ + 2 * ‖iteratedFDeriv ℝ n f₂ z‖ +
        ‖iteratedFDeriv ℝ n f₃ z‖ := by
  have ha : ContDiff ℝ ∞ (fun y => f₁ y - 2 * f₂ y) :=
    h₁.sub (contDiff_const.mul h₂)
  have hfst : ContDiff ℝ ∞ (fun y =>
      (f₁ y - 2 * f₂ y) • ContinuousLinearMap.fst ℝ ℝ ℝ) := ha.smul contDiff_const
  have hsnd : ContDiff ℝ ∞ (fun y =>
      f₃ y • ContinuousLinearMap.snd ℝ ℝ ℝ) := h₃.smul contDiff_const
  rw [fun_iteratedFDeriv_add_apply
    (contDiff_infty.mp hfst n).contDiffAt (contDiff_infty.mp hsnd n).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [norm_iteratedFDeriv_smul_fixed ha, norm_iteratedFDeriv_smul_fixed h₃]
  simp only [ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd, mul_one]
  gcongr
  have htwo : ContDiff ℝ ∞ (fun y => 2 * f₂ y) := contDiff_const.mul h₂
  rw [fun_iteratedFDeriv_sub_apply (contDiff_infty.mp h₁ n).contDiffAt
    (contDiff_infty.mp htwo n).contDiffAt]
  apply (norm_sub_le _ _).trans
  have heq : (fun y => 2 * f₂ y) = (2 : ℝ) • f₂ := by rfl
  rw [heq, iteratedFDeriv_const_smul_apply (contDiff_infty.mp h₂ n).contDiffAt,
    norm_smul]
  norm_num

/-- A uniform recurrence for jets of every member of the stable family. -/
theorem norm_iteratedFDeriv_cuspKernel_succ_le {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (n k : ℕ) (P : Polynomial ℝ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ (n + 1) (cuspKernel β tStar k P g) z‖ ≤
      ‖iteratedFDeriv ℝ n
        (cuspKernel β tStar (k + 1) (nextLogFlatPolynomial β k P) g) z‖ +
      2 * ‖iteratedFDeriv ℝ n
        (cuspKernel β tStar (k + 1) P (cuspNormalProfile g)) z‖ +
      ‖iteratedFDeriv ℝ n (cuspKernel β tStar (k + 2) P (deriv g)) z‖ := by
  rw [← norm_iteratedFDeriv_fderiv, cuspKernel_fderiv_eq hβ hStar k P hg hgc]
  exact norm_iteratedFDeriv_frame_le
    (contDiff_cuspKernel hβ hStar _ _ hg hgc)
    (contDiff_cuspKernel hβ hStar _ _ (contDiff_cuspNormalProfile hg)
      (hasCompactSupport_cuspNormalProfile hgc))
    (contDiff_cuspKernel hβ hStar _ _ (contDiff_infty_iff_deriv.mp hg).2 hgc.deriv) n z

/-- Every fixed Fréchet jet retains any smaller positive log-flat coefficient.
The bound is uniform in the entire tangential line and includes `t = 0`. -/
theorem exists_cuspKernel_jet_margin_bound {β β₁ tStar t₀ : ℝ}
    (hβ₁ : 0 < β₁) (hgap : β₁ < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (n k : ℕ) (P : Polynomial ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ C > 0, ∀ t ∈ Icc 0 t₀, ∀ u : ℝ,
      ‖iteratedFDeriv ℝ n (cuspKernel β tStar k P g) (t, u)‖ ≤
        C * logFlat β₁ tStar t := by
  induction n generalizing k P g with
  | zero =>
      obtain ⟨C, hC, hnormal⟩ :=
        exists_weightedLogFlat_margin_bound hβ₁ hgap hStar ht₀ k P
      obtain ⟨D, hD, hprofile⟩ := compactSmooth_bounded hg hgc
      refine ⟨C * D, mul_pos hC hD, ?_⟩
      intro t ht u
      rw [norm_iteratedFDeriv_zero]
      change ‖weightedLogFlat β tStar k P t * g (u / t ^ 2)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ (C * logFlat β₁ tStar t) * D :=
          mul_le_mul (hnormal t ht) (hprofile _) (abs_nonneg _)
            (mul_nonneg hC.le (logFlat_nonneg _ _ _))
        _ = _ := by ring
  | succ n ih =>
      obtain ⟨C₁, hC₁, h₁⟩ := ih (k + 1) (nextLogFlatPolynomial β k P) hg hgc
      obtain ⟨C₂, hC₂, h₂⟩ := ih (k + 1) P
        (contDiff_cuspNormalProfile hg) (hasCompactSupport_cuspNormalProfile hgc)
      obtain ⟨C₃, hC₃, h₃⟩ := ih (k + 2) P
        (contDiff_infty_iff_deriv.mp hg).2 hgc.deriv
      refine ⟨C₁ + 2 * C₂ + C₃, by positivity, ?_⟩
      intro t ht u
      calc
        _ ≤ ‖iteratedFDeriv ℝ n
              (cuspKernel β tStar (k + 1) (nextLogFlatPolynomial β k P) g) (t, u)‖ +
            2 * ‖iteratedFDeriv ℝ n
              (cuspKernel β tStar (k + 1) P (cuspNormalProfile g)) (t, u)‖ +
            ‖iteratedFDeriv ℝ n (cuspKernel β tStar (k + 2) P (deriv g)) (t, u)‖ :=
          norm_iteratedFDeriv_cuspKernel_succ_le (hβ₁.trans hgap) hStar n k P hg hgc (t, u)
        _ ≤ C₁ * logFlat β₁ tStar t + 2 * (C₂ * logFlat β₁ tStar t) +
            C₃ * logFlat β₁ tStar t := by
          exact add_le_add
            (add_le_add (h₁ t ht u)
              (mul_le_mul_of_nonneg_left (h₂ t ht u) (by norm_num))) (h₃ t ht u)
        _ = _ := by ring

end InfiniteZero
