import InfiniteZero.SchurGroundExistence
import InfiniteZero.OrthogonalSchurGeometry

/-!
# Quantitative estimates for the reconstructed Schur vector

Complement coercivity bounds the actual domain correction by the coupling.
The scalar equation then bounds the energy shift quadratically. These
estimates need no smallness or decay assumption on the coupling itself.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The compressed equation and the lower bound alone control the correction;
self-adjointness has already served to construct these data. -/
theorem schur_correction_norm_le (A : H →ₗ.[ℂ] H) (φ : A.domain)
    {E E₀ g : ℝ} (hg : 0 < g) (hE : E ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      (E₀ + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re)
    (ζ : (orthogonalCompression A (φ : H)).domain)
    (hζ : orthogonalCompression A (φ : H) ζ =
      schurCoupling A φ + (E : ℂ) • (ζ : orthogonalComplement (φ : H))) :
    ‖(ζ : orthogonalComplement (φ : H))‖ ≤ ‖schurCoupling A φ‖ / g := by
  have hc := shiftedOperator_coercive (orthogonalCompression A (φ : H))
    (orthogonalCompression_lower_bound A φ hbound) hE
  have hn := coerciveOperator_norm_lower
    (shiftedOperator (orthogonalCompression A (φ : H)) E) hc ζ
  rw [shiftedOperator_apply, hζ, add_sub_cancel_right] at hn
  exact (le_div_iff₀ hg).mpr (by simpa only [mul_comm] using hn)

/-- The Schur energy lies below the diagonal, with a quadratic coupling error. -/
theorem schur_energy_shift_bounds (A : H →ₗ.[ℂ] H) (φ : A.domain)
    {E E₀ g : ℝ} (hg : 0 < g) (hE : E ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      (E₀ + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re)
    (ζ : (orthogonalCompression A (φ : H)).domain)
    (hζ : orthogonalCompression A (φ : H) ζ =
      schurCoupling A φ + (E : ℂ) • (ζ : orthogonalComplement (φ : H)))
    (hscalar : inner ℂ (φ : H) (A φ) - (E : ℂ) -
      inner ℂ (schurCoupling A φ) (ζ : orthogonalComplement (φ : H)) = 0) :
    0 ≤ schurDiagonal A φ - E ∧
      schurDiagonal A φ - E ≤ ‖schurCoupling A φ‖ ^ 2 / g := by
  have hs := congrArg Complex.re hscalar
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hs
  have heq : schurDiagonal A φ - E =
      (inner ℂ (schurCoupling A φ) (ζ : orthogonalComplement (φ : H))).re := by
    dsimp only [schurDiagonal]
    linarith only [hs]
  rw [heq]
  constructor
  · have hc := shiftedOperator_coercive (orthogonalCompression A (φ : H))
      (orthogonalCompression_lower_bound A φ hbound) hE ζ
    rw [shiftedOperator_apply, hζ, add_sub_cancel_right] at hc
    have hsym : (inner ℂ (ζ : orthogonalComplement (φ : H)) (schurCoupling A φ)).re =
        (inner ℂ (schurCoupling A φ) (ζ : orthogonalComplement (φ : H))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    exact (mul_nonneg hg.le (sq_nonneg _)).trans (hc.trans_eq hsym)
  · calc
      _ ≤ ‖schurCoupling A φ‖ * ‖(ζ : orthogonalComplement (φ : H))‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ ‖schurCoupling A φ‖ * (‖schurCoupling A φ‖ / g) :=
        mul_le_mul_of_nonneg_left (schur_correction_norm_le A φ hg hE hbound ζ hζ)
          (norm_nonneg _)
      _ = _ := by ring

/-- Positive normalization coefficient for a unit reference vector minus an
orthogonal correction. -/
def schurNormalization (ζ : H) : ℝ := (Real.sqrt (1 + ‖ζ‖ ^ 2))⁻¹

omit [InnerProductSpace ℂ H] in
theorem schurNormalization_pos (ζ : H) : 0 < schurNormalization ζ := by
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

omit [InnerProductSpace ℂ H] in
theorem schurNormalization_le_one (ζ : H) : schurNormalization ζ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact Real.one_le_sqrt.mpr (by linarith [sq_nonneg ‖ζ‖])

omit [InnerProductSpace ℂ H] in
/-- The loss of the reference coefficient is quadratic in the correction. -/
theorem one_sub_schurNormalization_le (ζ : H) :
    1 - schurNormalization ζ ≤ ‖ζ‖ ^ 2 := by
  have hlo : 1 ≤ Real.sqrt (1 + ‖ζ‖ ^ 2) :=
    Real.one_le_sqrt.mpr (by linarith [sq_nonneg ‖ζ‖])
  have hhi : Real.sqrt (1 + ‖ζ‖ ^ 2) ≤ 1 + ‖ζ‖ ^ 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (‖ζ‖ ^ 2)]⟩
  have hm : schurNormalization ζ * Real.sqrt (1 + ‖ζ‖ ^ 2) = 1 :=
    inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one hlo))
  have hb := mul_le_mul_of_nonneg_right (schurNormalization_le_one ζ)
    (sub_nonneg.mpr hlo)
  nlinarith only [hm, hb, hhi]

omit [InnerProductSpace ℂ H] in
theorem half_le_schurNormalization {ζ : H} (hζ : ‖ζ‖ ≤ 1) :
    (1 / 2 : ℝ) ≤ schurNormalization ζ := by
  have hs : Real.sqrt (1 + ‖ζ‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg ζ]⟩
  have hpos : 0 < Real.sqrt (1 + ‖ζ‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [schurNormalization, ← one_div]
  exact (le_div_iff₀ hpos).mpr (by linarith only [hs])

end InfiniteZero
