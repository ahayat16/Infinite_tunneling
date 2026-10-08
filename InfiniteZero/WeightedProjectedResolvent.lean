import InfiniteZero.WeightedCompression

/-! From a weighted compressed inverse estimate to an operator bound on
the full Hilbert space, including the noncommuting projection. -/

noncomputable section
namespace InfiniteZero
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual conjugated, projected resolvent. The projection stays between
the resolvent and the inverse weight; it is not assumed to commute. -/
def weightedProjectedResolvent (φ : H) (M N : H →L[ℂ] H)
    (R : orthogonalComplement φ →L[ℂ] orthogonalComplement φ) : H →L[ℂ] H :=
  M.comp ((orthogonalComplement φ).subtypeL.comp
    (R.comp ((complementProjection φ).comp N)))

omit [CompleteSpace H] in
theorem norm_weighted_complementProjection_le (φ : H) (hφ : ‖φ‖ = 1)
    (M N : H →L[ℂ] H) (hMN : ∀ v, M (N v) = v)
    (hN : ∀ v, ‖N v‖ ≤ ‖v‖) (v : H) :
    ‖M (complementProjection φ (N v) : H)‖ ≤ (1 + ‖M φ‖) * ‖v‖ := by
  rw [complementProjection_coe φ hφ, map_sub, map_smul, hMN]
  have hi : ‖inner ℂ φ (N v)‖ ≤ ‖v‖ := by
    exact (norm_inner_le_norm φ (N v)).trans (by simpa only [hφ, one_mul] using hN v)
  calc
    _ ≤ ‖v‖ + ‖inner ℂ φ (N v) • M φ‖ := norm_sub_le _ _
    _ = ‖v‖ + ‖inner ℂ φ (N v)‖ * ‖M φ‖ := by rw [norm_smul]
    _ ≤ ‖v‖ + ‖v‖ * ‖M φ‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    _ = _ := by ring

omit [CompleteSpace H] in
/-- A compressed bound gives the full conjugated operator bound. Its extra
factor is precisely the cost of the orthogonal projection after weighting. -/
theorem norm_weightedProjectedResolvent_le (φ : H) (hφ : ‖φ‖ = 1)
    (M N : H →L[ℂ] H) (hMN : ∀ v, M (N v) = v)
    (hN : ∀ v, ‖N v‖ ≤ ‖v‖)
    (R : orthogonalComplement φ →L[ℂ] orthogonalComplement φ)
    {c : ℝ} (hc : 0 < c)
    (hR : ∀ f : orthogonalComplement φ, c * ‖M (R f : H)‖ ≤ ‖M (f : H)‖) :
    ‖weightedProjectedResolvent φ M N R‖ ≤ (1 + ‖M φ‖) / c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h := (hR (complementProjection φ (N v))).trans
    (norm_weighted_complementProjection_le φ hφ M N hMN hN v)
  change ‖M (R (complementProjection φ (N v)) : H)‖ ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm c] using h

end InfiniteZero
