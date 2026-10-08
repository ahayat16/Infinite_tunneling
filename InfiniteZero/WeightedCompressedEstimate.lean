import InfiniteZero.WeightedCompression

/-!
# Weighted estimates on the actual compressed domain

A rank-one weighted inequality on the original operator domain gives a norm
estimate for its orthogonal compression after absorbing the reference-vector
defect and residual. The estimate uses the exact lifting identity and never
assumes that the multiplier preserves an operator domain.
-/

noncomputable section

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section

variable (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (E₀ : ℝ) (r : H)
    (hr : A φ = (E₀ : ℂ) • (φ : H) + r)
    (M : H →L[ℂ] H) (hM : IsSelfAdjoint M)
    (hMnorm : ∀ u : H, ‖u‖ ≤ ‖M u‖)
    {g k c E : ℝ} (hk : 0 ≤ k) (hc : 0 < c) (hE : E ≤ E₀)
    (hbound : ∀ u : A.domain,
      g * ‖M (u : H)‖ ^ 2 - k * ‖inner ℂ (φ : H) (M (u : H))‖ ^ 2 ≤
        (inner ℂ (M (u : H)) (M (A u))).re - E₀ * ‖M (u : H)‖ ^ 2)
    (habsorb : c + k * ‖M (φ : H) - (φ : H)‖ ^ 2 + ‖r‖ * ‖M (φ : H)‖ ≤ g)

include hA hφ hr hM hMnorm hk hc hE hbound habsorb

/-- Coercivity for every vector in the genuine compressed operator domain. -/
theorem weighted_compression_norm_lower
    (ζ : (orthogonalCompression A (φ : H)).domain) :
    c * ‖M ((ζ : orthogonalComplement (φ : H)) : H)‖ ≤
      ‖M (shiftedOperator (orthogonalCompression A (φ : H)) E ζ : H)‖ := by
  let u := compressionDomainInclusion A (φ : H) ζ
  let v : H := (shiftedOperator (orthogonalCompression A (φ : H)) E ζ : H)
  let t : ℂ := inner ℂ r ((ζ : orthogonalComplement (φ : H)) : H)
  have hu : inner ℂ (φ : H) (u : H) = 0 :=
    orthogonalComplement_inner_right (φ : H) (ζ : orthogonalComplement (φ : H))
  have hoverlap := weighted_orthogonality_defect_le_weighted_norm M hM hMnorm
    (φ : H) (u : H) hu
  have hpenalty : k * ‖inner ℂ (φ : H) (M (u : H))‖ ^ 2 ≤
      k * ‖M (φ : H) - (φ : H)‖ ^ 2 * ‖M (u : H)‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hoverlap
    simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left hs hk
  have ht : ‖t‖ ≤ ‖r‖ * ‖M (u : H)‖ :=
    (norm_inner_le_norm r (u : H)).trans
      (mul_le_mul_of_nonneg_left (hMnorm (u : H)) (norm_nonneg r))
  have hlift : shiftedOperator A E u = v + t • (φ : H) :=
    compression_lift_shifted_eq_of_residual A hA φ hφ E₀ r hr E ζ
  have hshift :
      (inner ℂ (M (u : H)) (M (shiftedOperator A E u))).re =
        (inner ℂ (M (u : H)) (M (A u))).re - E * ‖M (u : H)‖ ^ 2 := by
    have hn : (inner ℂ (M (u : H)) (M (u : H))).re = ‖M (u : H)‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (M (u : H))).symm
    rw [shiftedOperator_apply, map_sub, map_smul, inner_sub_right, inner_smul_right,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hn]
  have hbase : g * ‖M (u : H)‖ ^ 2 -
      k * ‖inner ℂ (φ : H) (M (u : H))‖ ^ 2 ≤
      (inner ℂ (M (u : H)) (M (shiftedOperator A E u))).re := by
    rw [hshift]
    have henergy := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖M (u : H)‖)
    linarith only [hbound u, henergy]
  have hmain : (inner ℂ (M (u : H)) (M v)).re ≤ ‖M (u : H)‖ * ‖M v‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hres : (inner ℂ (M (u : H)) (t • M (φ : H))).re ≤
      (‖r‖ * ‖M (φ : H)‖) * ‖M (u : H)‖ ^ 2 := by
    calc
      _ ≤ ‖M (u : H)‖ * ‖t • M (φ : H)‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ = (‖M (u : H)‖ * ‖M (φ : H)‖) * ‖t‖ := by rw [norm_smul]; ring
      _ ≤ (‖M (u : H)‖ * ‖M (φ : H)‖) * (‖r‖ * ‖M (u : H)‖) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have hsum : (inner ℂ (M (u : H)) (M (shiftedOperator A E u))).re =
      (inner ℂ (M (u : H)) (M v)).re +
        (inner ℂ (M (u : H)) (t • M (φ : H))).re := by
    rw [hlift, map_add, map_smul, inner_add_right, Complex.add_re]
  have habsorb' := mul_le_mul_of_nonneg_right habsorb (sq_nonneg ‖M (u : H)‖)
  have hsq : c * ‖M (u : H)‖ ^ 2 ≤ ‖M (u : H)‖ * ‖M v‖ := by
    nlinarith only [hbase, hpenalty, hmain, hres, hsum, habsorb']
  change c * ‖M (u : H)‖ ≤ ‖M v‖
  by_cases hz : ‖M (u : H)‖ = 0
  · simpa only [hz, mul_zero] using norm_nonneg (M v)
  · have hpos : 0 < ‖M (u : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ (mul_pos hc hpos)).mp
    have hsq' := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith only [hsq']

/-- Division form of the estimate for a positive absorbed constant. -/
theorem weighted_compression_norm_le
    (ζ : (orthogonalCompression A (φ : H)).domain) :
    ‖M ((ζ : orthogonalComplement (φ : H)) : H)‖ ≤
      ‖M (shiftedOperator (orthogonalCompression A (φ : H)) E ζ : H)‖ / c := by
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using
    weighted_compression_norm_lower A hA φ hφ E₀ r hr M hM hMnorm hk hc hE hbound habsorb ζ

/-- Any actual compressed resolvent satisfies the weighted estimate, by its
graph identity. Its existence is not an assumption hidden in a norm bound. -/
theorem weighted_compression_resolvent_bound
    (R : orthogonalComplement (φ : H) →L[ℂ] orthogonalComplement (φ : H))
    (hR : IsOperatorResolvent (orthogonalCompression A (φ : H)) E R)
    (f : orthogonalComplement (φ : H)) :
    ‖M (R f : H)‖ ≤ ‖M (f : H)‖ / c := by
  obtain ⟨ζ, hζ, hCζ⟩ := (orthogonalCompression A (φ : H)).mem_graph_iff.mp (hR f)
  have hshift : shiftedOperator (orthogonalCompression A (φ : H)) E ζ = f := by
    rw [shiftedOperator_apply, hCζ, hζ, add_sub_cancel_right]
  have h := weighted_compression_norm_le A hA φ hφ E₀ r hr M hM hMnorm hk hc hE
    hbound habsorb ζ
  simpa only [hζ, hshift] using h

end
end InfiniteZero
