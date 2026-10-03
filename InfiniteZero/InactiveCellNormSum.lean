import InfiniteZero.InactiveCellL1Bounds

/-! The sum of seven absolute cell values, as required by the manuscript. -/

noncomputable section

namespace InfiniteZero

/-- The seven absolute values; neither active ordered pair is included. -/
def inactiveCellNormSum (I : Fin 3 → Fin 3 → ℂ) : ℝ :=
  ‖I 0 0‖ + ‖I 0 1‖ + ‖I 0 2‖ + ‖I 1 0‖ + ‖I 1 1‖ + ‖I 2 0‖ + ‖I 2 2‖

theorem inactiveCellNormSum_eq_sum (I : Fin 3 → Fin 3 → ℂ) :
    inactiveCellNormSum I = ∑ i : Fin 3, ∑ j : Fin 3,
      if (i, j) = (1, 2) ∨ (i, j) = (2, 1) then 0 else ‖I i j‖ := by
  simp [inactiveCellNormSum, Fin.sum_univ_succ]
  ring

theorem inactiveCellNormSum_nonneg (I : Fin 3 → Fin 3 → ℂ) :
    0 ≤ inactiveCellNormSum I := by
  unfold inactiveCellNormSum
  positivity

theorem norm_inactiveCells_le_normSum (I : Fin 3 → Fin 3 → ℂ) :
    ‖inactiveCells I‖ ≤ inactiveCellNormSum I := by
  unfold inactiveCells inactiveCellNormSum
  exact norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le
      (norm_add_le _ _) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl

theorem inactiveCellNormSum_le_of_bound {I : Fin 3 → Fin 3 → ℂ} {B : ℝ}
    (hbound : ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) → ‖I i j‖ ≤ B) :
    inactiveCellNormSum I ≤ 7 * B := by
  have h00 := hbound 0 0 (by decide) (by decide)
  have h01 := hbound 0 1 (by decide) (by decide)
  have h02 := hbound 0 2 (by decide) (by decide)
  have h10 := hbound 1 0 (by decide) (by decide)
  have h11 := hbound 1 1 (by decide) (by decide)
  have h20 := hbound 2 0 (by decide) (by decide)
  have h22 := hbound 2 2 (by decide) (by decide)
  unfold inactiveCellNormSum
  linarith

end InfiniteZero
