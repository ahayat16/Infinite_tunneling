import InfiniteZero.CoerciveResolvent

/-!
# Removing an eigenvector from a shifted energy

Subtracting any multiple of an eigenvector of energy `E` leaves the shifted
quadratic energy unchanged. This algebraic identity takes place on the actual
operator domain and transfers a nonnegative complement bound to every vector.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The energy of `A - E` is the original energy minus the scalar mass term. -/
theorem re_inner_shiftedOperator (A : H →ₗ.[ℂ] H) (E : ℝ) (u : A.domain) :
    (inner ℂ (u : H) (shiftedOperator A E u)).re =
      (inner ℂ (u : H) (A u)).re - E * ‖(u : H)‖ ^ 2 := by
  rw [shiftedOperator_apply, inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hn : (inner ℂ (u : H) (u : H)).re = ‖(u : H)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (u : H)).symm
  rw [hn]

variable [CompleteSpace H]

/-- Subtracting a multiple of an eigenvector does not change the shifted energy. -/
theorem eigenvector_shiftedEnergy_sub (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {E : ℝ} (w : A.domain) (hw : A w = (E : ℂ) • (w : H))
    (u : A.domain) (a : ℂ) :
    (inner ℂ (u : H) (A u)).re - E * ‖(u : H)‖ ^ 2 =
      (inner ℂ ((u - a • w : A.domain) : H) (A (u - a • w))).re -
        E * ‖((u - a • w : A.domain) : H)‖ ^ 2 := by
  let T := shiftedOperator A E
  have hTw : T w = 0 := by simp only [T, shiftedOperator_apply, hw, sub_self]
  have horth : inner ℂ (w : H) (T u) = 0 := by
    have h := selfAdjoint_inner_of_mem_graph (isSelfAdjoint_shiftedOperator A hA E)
      (T.mem_graph w) (T.mem_graph u)
    change inner ℂ (T w) (u : H) = inner ℂ (w : H) (T u) at h
    simpa only [hTw, inner_zero_left] using h.symm
  have hsub : T (u - a • w) = T u := by
    calc
      T (u - a • w) = T u - T (a • w) := T.map_sub u (a • w)
      _ = T u - a • T w := congrArg (fun z : H => T u - z) (T.map_smul a w)
      _ = T u := by rw [hTw, smul_zero, sub_zero]
  rw [← re_inner_shiftedOperator A E u, ← re_inner_shiftedOperator A E (u - a • w)]
  change (inner ℂ (u : H) (T u)).re =
    (inner ℂ ((u - a • w : A.domain) : H) (T (u - a • w))).re
  rw [hsub]
  change (inner ℂ (u : H) (T u)).re = (inner ℂ ((u : H) - a • (w : H)) (T u)).re
  rw [inner_sub_left, inner_smul_left, horth, mul_zero, sub_zero]

/-- A nonnegative shifted form on the orthogonal complement of a nonzero
eigenvector is nonnegative on the whole operator domain. -/
theorem shiftedEnergy_nonneg_of_complement (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {E g : ℝ} (hg : 0 ≤ g) (w : A.domain) (hw0 : (w : H) ≠ 0)
    (hw : A w = (E : ℂ) • (w : H))
    (hbound : ∀ u : A.domain, inner ℂ (w : H) (u : H) = 0 →
      g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re - E * ‖(u : H)‖ ^ 2)
    (u : A.domain) :
    0 ≤ (inner ℂ (u : H) (A u)).re - E * ‖(u : H)‖ ^ 2 := by
  let a : ℂ := inner ℂ (w : H) (u : H) / inner ℂ (w : H) (w : H)
  have hww : inner ℂ (w : H) (w : H) ≠ 0 := by
    intro h
    exact hw0 ((inner_self_eq_zero (𝕜 := ℂ)).mp h)
  have horth : inner ℂ (w : H) ((u - a • w : A.domain) : H) = 0 := by
    change inner ℂ (w : H) ((u : H) - a • (w : H)) = 0
    rw [inner_sub_right, inner_smul_right]
    dsimp only [a]
    rw [div_mul_cancel₀ _ hww, sub_self]
  rw [eigenvector_shiftedEnergy_sub A hA w hw u a]
  exact (mul_nonneg hg (sq_nonneg _)).trans (hbound (u - a • w) horth)

end InfiniteZero
