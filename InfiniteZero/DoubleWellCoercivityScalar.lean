import InfiniteZero.OverlapDecayScalar

/-!
# Absorbing the fixed losses of two-well localization

The atomic gap is `γ * coupling`. Two overlap errors each cost at most
`2γ * coupling * C / coupling²`, and two IMS errors cost `2D`.
One fixed threshold absorbs both losses, leaving half the atomic gap.
The same threshold makes the exterior negative-energy reserve sufficient.
-/

noncomputable section
namespace InfiniteZero

theorem exists_twoWell_coercivity_absorption_threshold
    {γ : ℝ} (hγ : 0 < γ) (C D B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      0 < coupling ∧
      γ * coupling ≤ coupling ^ 2 - B * coupling ∧
      γ / 2 * coupling ≤
        γ * coupling - 4 * (γ * coupling) * (C / coupling ^ 2) - 2 * D := by
  let T := max 1 (max (16 * C) (max (8 * D / γ) (B + γ)))
  refine ⟨T, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have h1 : 1 ≤ coupling := (le_max_left _ _).trans hc
  have hrest : max (16 * C) (max (8 * D / γ) (B + γ)) ≤ coupling :=
    (le_max_right _ _).trans hc
  have hC : 16 * C ≤ coupling := (le_max_left _ _).trans hrest
  have hrest' : max (8 * D / γ) (B + γ) ≤ coupling :=
    (le_max_right _ _).trans hrest
  have hD : 8 * D / γ ≤ coupling := (le_max_left _ _).trans hrest'
  have hB : B + γ ≤ coupling := (le_max_right _ _).trans hrest'
  have hcpos : 0 < coupling := zero_lt_one.trans_le h1
  have htail : C / coupling ^ 2 ≤ 1 / 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos hcpos)).mpr
    have hs := mul_le_mul_of_nonneg_right h1 hcpos.le
    nlinarith only [hs, hC]
  have hloss := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ 4 * (γ * coupling) by positivity)
  have hims := (div_le_iff₀ hγ).mp hD
  refine ⟨hcpos, ?_, ?_⟩
  · have he := mul_le_mul_of_nonneg_right hB hcpos.le
    nlinarith only [he]
  · nlinarith only [hloss, hims]

end InfiniteZero
