import InfiniteZero.OrthogonalCompression

/-!
# Hilbert-space geometry of a Schur ground vector

The convention is that the complex inner product is linear in the second
variable. Orthogonality to `φ - ζ` fixes the coefficient of `φ` and gives the
norm bound needed to transfer coercivity of the compressed operator to a gap
above the reconstructed eigenvector.
-/

noncomputable section

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem orthogonalComplement_inner_right (φ : H) (ζ : orthogonalComplement φ) :
    inner ℂ φ (ζ : H) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp ζ.property

theorem orthogonalComplement_inner_left (φ : H) (ζ : orthogonalComplement φ) :
    inner ℂ (ζ : H) φ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left.mp ζ.property

/-- Exact normalization of the reconstructed Schur vector. -/
theorem schur_groundVector_norm_sq (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) :
    ‖φ - (ζ : H)‖ ^ 2 = 1 + ‖ζ‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), hφ, orthogonalComplement_inner_right]
  simp

theorem schur_groundVector_ne_zero (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) : φ - (ζ : H) ≠ 0 := by
  intro hz
  have hn := schur_groundVector_norm_sq φ hφ ζ
  rw [hz, norm_zero, zero_pow (by decide)] at hn
  nlinarith [sq_nonneg ‖ζ‖]

/-- Pythagoras in the original orthogonal decomposition. -/
theorem schur_decomposition_norm_sq (φ : H) (hφ : ‖φ‖ = 1)
    (a : ℂ) (η : orthogonalComplement φ) :
    ‖a • φ + (η : H)‖ ^ 2 = ‖a‖ ^ 2 + ‖η‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_left, orthogonalComplement_inner_right]
  simp [norm_smul, hφ]

/-- Orthogonality to `φ - ζ` identifies the scalar coefficient exactly. -/
theorem schur_orthogonality_coefficient (φ : H) (hφ : ‖φ‖ = 1)
    (a : ℂ) (ζ η : orthogonalComplement φ)
    (horth : inner ℂ (φ - (ζ : H)) (a • φ + (η : H)) = 0) :
    a = inner ℂ (ζ : H) (η : H) := by
  have hself : inner ℂ φ φ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]
    norm_num
  simp only [inner_sub_left, inner_add_right, inner_smul_right, hself,
    orthogonalComplement_inner_right, orthogonalComplement_inner_left,
    sub_zero, zero_sub, mul_one] at horth
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using horth)

/-- Exact square identity behind the gap transfer. -/
theorem schur_complement_norm_sq (φ : H) (hφ : ‖φ‖ = 1)
    (a : ℂ) (ζ η : orthogonalComplement φ)
    (horth : inner ℂ (φ - (ζ : H)) (a • φ + (η : H)) = 0) :
    ‖(η : H) + a • (ζ : H)‖ ^ 2 =
      ‖η‖ ^ 2 + (2 + ‖ζ‖ ^ 2) * ‖a‖ ^ 2 := by
  have ha := schur_orthogonality_coefficient φ hφ a ζ η horth
  rw [add_comm, norm_add_sq (𝕜 := ℂ), inner_smul_left, ← ha]
  simp only [norm_smul, mul_pow]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  change ‖a‖ ^ 2 * ‖ζ‖ ^ 2 + 2 * ((‖a‖ ^ 2 : ℝ) : ℂ).re + ‖η‖ ^ 2 = _
  rw [Complex.ofReal_re]
  ring

/-- Coercivity on the shifted complement controls the full norm orthogonal to
the Schur eigenvector. No smallness of `ζ` is required. -/
theorem schur_complement_norm_sq_ge (φ : H) (hφ : ‖φ‖ = 1)
    (a : ℂ) (ζ η : orthogonalComplement φ)
    (horth : inner ℂ (φ - (ζ : H)) (a • φ + (η : H)) = 0) :
    ‖a • φ + (η : H)‖ ^ 2 ≤ ‖(η : H) + a • (ζ : H)‖ ^ 2 := by
  rw [schur_decomposition_norm_sq φ hφ a η,
    schur_complement_norm_sq φ hφ a ζ η horth]
  nlinarith [sq_nonneg ‖a‖, mul_nonneg (sq_nonneg ‖ζ‖) (sq_nonneg ‖a‖)]

end InfiniteZero
