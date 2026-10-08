import InfiniteZero.SchurGroundEstimates

/-!
# Normalization and comparison of the Schur vector

For a unit vector `φ` and an orthogonal correction `ζ`, the positive
coefficient `schurNormalization ζ` is exactly the reciprocal norm of
`φ - ζ`. The resulting vector is normalized, has positive overlap with `φ`,
and differs from `φ` by at most twice the norm of the correction. These
statements use Hilbert-space geometry only, without decay assumptions.
-/

noncomputable section

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Schur vector normalized with a positive real coefficient. -/
def normalizedSchurVector (φ : H) (ζ : orthogonalComplement φ) : H :=
  (schurNormalization (ζ : H) : ℂ) • (φ - (ζ : H))

/-- Pythagoras identifies the explicit normalization with the reciprocal norm. -/
theorem schurNormalization_eq_inv_norm (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) :
    schurNormalization (ζ : H) = ‖φ - (ζ : H)‖⁻¹ := by
  unfold schurNormalization
  change (Real.sqrt (1 + ‖ζ‖ ^ 2))⁻¹ = ‖φ - (ζ : H)‖⁻¹
  have hn := schur_groundVector_norm_sq φ hφ ζ
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]

theorem normalizedSchurVector_norm (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) : ‖normalizedSchurVector φ ζ‖ = 1 := by
  rw [normalizedSchurVector, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (schurNormalization_pos _),
    schurNormalization_eq_inv_norm φ hφ ζ]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (schur_groundVector_ne_zero φ hφ ζ))

/-- The phase convention fixes the overlap to the positive normalization coefficient. -/
theorem inner_normalizedSchurVector (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) :
    inner ℂ φ (normalizedSchurVector φ ζ) = (schurNormalization (ζ : H) : ℂ) := by
  have hs : inner ℂ φ φ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]
    norm_num
  rw [normalizedSchurVector, inner_smul_right, inner_sub_right, hs,
    orthogonalComplement_inner_right, sub_zero, mul_one]

omit [InnerProductSpace ℂ H] in
/-- A linear bound for the loss of normalization, valid for arbitrary corrections. -/
theorem one_sub_schurNormalization_le_norm (ζ : H) :
    1 - schurNormalization ζ ≤ ‖ζ‖ := by
  by_cases hζ : ‖ζ‖ ≤ 1
  · exact (one_sub_schurNormalization_le ζ).trans (by nlinarith [norm_nonneg ζ])
  · have hc := schurNormalization_pos ζ
    have hn := le_of_not_ge hζ
    linarith

theorem normalizedSchurVector_sub_norm_le_loss (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) :
    ‖normalizedSchurVector φ ζ - φ‖ ≤
      (1 - schurNormalization (ζ : H)) + ‖ζ‖ := by
  let c := schurNormalization (ζ : H)
  have hc : 0 < c := schurNormalization_pos _
  have hc1 : c ≤ 1 := schurNormalization_le_one _
  have heq : normalizedSchurVector φ ζ - φ =
      ((c - 1 : ℝ) : ℂ) • φ - (c : ℂ) • (ζ : H) := by
    simp only [normalizedSchurVector, Complex.ofReal_sub, Complex.ofReal_one, c]
    module
  calc
    ‖normalizedSchurVector φ ζ - φ‖ ≤
        ‖((c - 1 : ℝ) : ℂ) • φ‖ + ‖(c : ℂ) • (ζ : H)‖ := by
      rw [heq]
      exact norm_sub_le _ _
    _ = (1 - c) + c * ‖ζ‖ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, hφ,
        abs_of_nonpos (sub_nonpos.mpr hc1), abs_of_pos hc]
      simp only [mul_one, neg_sub, Submodule.norm_coe]
    _ ≤ _ := by
      have hm := mul_le_of_le_one_left (norm_nonneg ζ) hc1
      change (1 - c) + c * ‖ζ‖ ≤ (1 - c) + ‖ζ‖
      linarith

/-- A quadratic normalization error plus the correction itself. -/
theorem normalizedSchurVector_sub_norm_le_add_sq (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) :
    ‖normalizedSchurVector φ ζ - φ‖ ≤ ‖ζ‖ + ‖ζ‖ ^ 2 := by
  have h := normalizedSchurVector_sub_norm_le_loss φ hφ ζ
  have hc := one_sub_schurNormalization_le (ζ : H)
  change 1 - schurNormalization (ζ : H) ≤ ‖ζ‖ ^ 2 at hc
  linarith

/-- The normalized state is close to the reference whenever the correction is small;
the estimate itself needs no smallness hypothesis. -/
theorem normalizedSchurVector_sub_norm_le (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) :
    ‖normalizedSchurVector φ ζ - φ‖ ≤ 2 * ‖ζ‖ := by
  have h := normalizedSchurVector_sub_norm_le_loss φ hφ ζ
  have hc := one_sub_schurNormalization_le_norm (ζ : H)
  change 1 - schurNormalization (ζ : H) ≤ ‖ζ‖ at hc
  linarith

/-- Normalization preserves membership in an actual operator eigengraph. -/
theorem normalizedSchurVector_mem_graph (A : H →ₗ.[ℂ] H)
    (φ : H) (ζ : orthogonalComplement φ) (E : ℝ)
    (hgraph : (φ - (ζ : H), (E : ℂ) • (φ - (ζ : H))) ∈ A.graph) :
    (normalizedSchurVector φ ζ, (E : ℂ) • normalizedSchurVector φ ζ) ∈ A.graph := by
  have h := A.graph.smul_mem (schurNormalization (ζ : H) : ℂ) hgraph
  simpa only [Prod.smul_mk, normalizedSchurVector, smul_smul, mul_comm] using h

end InfiniteZero
