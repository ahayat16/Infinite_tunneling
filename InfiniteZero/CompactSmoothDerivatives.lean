import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform bounds for derivatives of compactly supported smooth profiles

All ingredients are standard Mathlib theorems.  This small interface provides
the closure under differentiation and global bounds used for cusp cutoffs.
-/

noncomputable section

open scoped ContDiff

namespace InfiniteZero

theorem hasCompactSupport_iteratedDeriv {g : ℝ → ℝ} (hg : HasCompactSupport g)
    (n : ℕ) : HasCompactSupport (iteratedDeriv n g) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem contDiff_iteratedDeriv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n g) := by
  rw [iteratedDeriv_eq_iterate]
  exact hg.iterate_deriv n

theorem compactSmooth_bounded {g : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ g)
    (hcompact : HasCompactSupport g) : ∃ C > 0, ∀ x : ℝ, |g x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    (hcompact.isCompact_range hsmooth.continuous).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun x => by simpa only [Real.norm_eq_abs] using hbound (g x) ⟨x, rfl⟩⟩

/-- Every derivative has its own positive uniform bound. -/
theorem compactSmooth_iteratedDeriv_bounded {g : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ g)
    (hcompact : HasCompactSupport g) (n : ℕ) :
    ∃ C > 0, ∀ x : ℝ, |iteratedDeriv n g x| ≤ C :=
  compactSmooth_bounded (contDiff_iteratedDeriv hsmooth n)
    (hasCompactSupport_iteratedDeriv hcompact n)

/-- A convenient differentiation-stable predicate for tangential profiles. -/
structure CompactSmooth (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  compactSupport : HasCompactSupport g

namespace CompactSmooth

theorem deriv {g : ℝ → ℝ} (hg : CompactSmooth g) : CompactSmooth (deriv g) :=
  ⟨(contDiff_infty_iff_deriv.mp hg.smooth).2, hg.compactSupport.deriv⟩

theorem iteratedDeriv {g : ℝ → ℝ} (hg : CompactSmooth g) (n : ℕ) :
    CompactSmooth (_root_.iteratedDeriv n g) :=
  ⟨contDiff_iteratedDeriv hg.smooth n, hasCompactSupport_iteratedDeriv hg.compactSupport n⟩

theorem bounded {g : ℝ → ℝ} (hg : CompactSmooth g) : ∃ C > 0, ∀ x : ℝ, |g x| ≤ C :=
  compactSmooth_bounded hg.smooth hg.compactSupport

theorem derivative_bounded {g : ℝ → ℝ} (hg : CompactSmooth g) (n : ℕ) :
    ∃ C > 0, ∀ x : ℝ, |_root_.iteratedDeriv n g x| ≤ C :=
  (hg.iteratedDeriv n).bounded

end CompactSmooth
end InfiniteZero
