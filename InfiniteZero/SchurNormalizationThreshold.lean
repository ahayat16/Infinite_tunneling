import InfiniteZero.SchurGroundEstimates
import InfiniteZero.SchurExponentialBounds

/-!
# A uniform normalization threshold for exponentially small corrections

The threshold is chosen before the correction vector. The loss of the
positive Schur normalization keeps the squared exponential decay rate.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H]

theorem exists_schurNormalization_exponential_threshold {K d : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) :
    ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling → ∀ ζ : H,
      ‖ζ‖ ≤ K * Real.exp (-d * coupling) →
        (1 / 2 : ℝ) ≤ schurNormalization ζ ∧
        0 ≤ 1 - schurNormalization ζ ∧
        1 - schurNormalization ζ ≤ K ^ 2 * Real.exp (-2 * d * coupling) := by
  refine ⟨max 1 (K / d), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro coupling hcoupling ζ hζ
  have hKd : K ≤ d * coupling := by
    have h := (div_le_iff₀ hd).mp ((le_max_right 1 (K / d)).trans hcoupling)
    simpa only [mul_comm coupling d] using h
  have hexp : K ≤ Real.exp (d * coupling) := by
    have h := Real.add_one_le_exp (d * coupling)
    linarith only [hKd, h]
  have hsmall : K * Real.exp (-d * coupling) ≤ 1 := by
    calc
      _ ≤ Real.exp (d * coupling) * Real.exp (-d * coupling) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  refine ⟨half_le_schurNormalization (hζ.trans hsmall),
    sub_nonneg.mpr (schurNormalization_le_one ζ), ?_⟩
  have hs : ‖ζ‖ ^ 2 ≤ (K * Real.exp (-d * coupling)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg ζ) (mul_nonneg hK (Real.exp_pos _).le)).mpr hζ
  calc
    1 - schurNormalization ζ ≤ ‖ζ‖ ^ 2 := one_sub_schurNormalization_le ζ
    _ ≤ (K * Real.exp (-d * coupling)) ^ 2 := hs
    _ = K ^ 2 * Real.exp (-2 * d * coupling) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring

end InfiniteZero
