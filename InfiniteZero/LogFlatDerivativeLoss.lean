import InfiniteZero.LogFlatSmooth
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A strict log-flat margin absorbs every fixed derivative loss

Inverse normal powers and polynomials in the logarithm are absorbed uniformly
on a fixed compact interval. The zero extension is included. The same estimate
holds for every fixed iterated derivative, by the differentiation-stable family
already established in `LogFlatSmooth`.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

theorem logFlat_nonneg (β tStar t : ℝ) : 0 ≤ logFlat β tStar t := by
  unfold logFlat
  split_ifs <;> positivity

theorem weightedLogFlat_eq_margin_mul (β β₁ tStar : ℝ) (k : ℕ)
    (P : Polynomial ℝ) (t : ℝ) :
    weightedLogFlat β tStar k P t =
      weightedLogFlat (β - β₁) tStar k P t * logFlat β₁ tStar t := by
  by_cases ht : 0 < t
  · simp only [weightedLogFlat, logFlat_of_pos _ _ ht]
    rw [show -β * (Real.log (tStar / t)) ^ 2 =
      -(β - β₁) * (Real.log (tStar / t)) ^ 2 +
        -β₁ * (Real.log (tStar / t)) ^ 2 by ring, Real.exp_add]
    ring
  · simp only [weightedLogFlat_of_nonpos _ _ _ _ (le_of_not_gt ht),
      logFlat_of_nonpos _ _ (le_of_not_gt ht), mul_zero]

/-- The constant is chosen before the normal variable. Only a strict margin
in the log-flat coefficient is spent, regardless of the polynomial loss. -/
theorem exists_weightedLogFlat_margin_bound {β β₁ tStar t₀ : ℝ}
    (_hβ₁ : 0 < β₁) (hgap : β₁ < β) (hStar : 0 < tStar) (_ht₀ : 0 < t₀)
    (k : ℕ) (P : Polynomial ℝ) :
    ∃ C > 0, ∀ t ∈ Icc 0 t₀,
      |weightedLogFlat β tStar k P t| ≤ C * logFlat β₁ tStar t := by
  have hc := (contDiff_weightedLogFlat (sub_pos.mpr hgap) hStar k P).continuous
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) t₀)).image hc).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t ht
  rw [weightedLogFlat_eq_margin_mul β β₁, abs_mul,
    abs_of_nonneg (logFlat_nonneg β₁ tStar t)]
  apply mul_le_mul_of_nonneg_right _ (logFlat_nonneg β₁ tStar t)
  simpa only [Real.norm_eq_abs] using hbound _ ⟨t, ht, rfl⟩

/-- Each fixed derivative retains any smaller positive log-flat coefficient.
No bound uniform in the derivative order is claimed. -/
theorem exists_iteratedDeriv_weightedLogFlat_margin_bound {β β₁ tStar t₀ : ℝ}
    (hβ₁ : 0 < β₁) (hgap : β₁ < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀)
    (n k : ℕ) (P : Polynomial ℝ) :
    ∃ C > 0, ∀ t ∈ Icc 0 t₀,
      |iteratedDeriv n (weightedLogFlat β tStar k P) t| ≤
        C * logFlat β₁ tStar t := by
  induction n generalizing k P with
  | zero =>
      simpa only [iteratedDeriv_zero] using
        exists_weightedLogFlat_margin_bound hβ₁ hgap hStar ht₀ k P
  | succ n ih =>
      simpa only [iteratedDeriv_succ', deriv_weightedLogFlat (hβ₁.trans hgap) hStar] using
        ih (k + 1) (nextLogFlatPolynomial β k P)

theorem exists_iteratedDeriv_logFlat_margin_bound {β β₁ tStar t₀ : ℝ}
    (hβ₁ : 0 < β₁) (hgap : β₁ < β) (hStar : 0 < tStar) (ht₀ : 0 < t₀) (n : ℕ) :
    ∃ C > 0, ∀ t ∈ Icc 0 t₀,
      |iteratedDeriv n (logFlat β tStar) t| ≤ C * logFlat β₁ tStar t := by
  have heq : weightedLogFlat β tStar 0 (1 : Polynomial ℝ) = logFlat β tStar := by
    funext t
    simp [weightedLogFlat]
  rw [← heq]
  exact exists_iteratedDeriv_weightedLogFlat_margin_bound hβ₁ hgap hStar ht₀ n 0 1

end InfiniteZero
