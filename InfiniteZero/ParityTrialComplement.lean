import InfiniteZero.L2Inversion

/-!
# Parity converts one trial orthogonality into two atomic orthogonalities

Within a fixed parity sector, the overlap with the reflected atom is
determined by the original overlap. Thus orthogonality to any nonzero
multiple of the matching signed sum removes both overlap terms.
-/

noncomputable section
namespace InfiniteZero

theorem inner_l2Inversion_left_eq_right (v u : L2Space) :
    inner ℂ (l2Inversion v) u = inner ℂ v (l2Inversion u) := by
  simpa only [l2Inversion_apply_twice] using inner_l2Inversion v (l2Inversion u)

theorem inner_l2Inversion_of_parity (even : Bool) {u : L2Space}
    (hu : HasL2Parity even u) (v : L2Space) :
    inner ℂ (l2Inversion v) u =
      if even then inner ℂ v u else -inner ℂ v u := by
  rw [inner_l2Inversion_left_eq_right,
    (l2Inversion_eq_iff_hasL2Parity even u).mpr hu]
  cases even <;> simp

/-- Inside a fixed parity sector, orthogonality to its signed trial sum
forces orthogonality to both original reference states. -/
theorem parity_trial_complement_orthogonal (even : Bool) (v u : L2Space)
    (hu : HasL2Parity even u) {z : ℂ} (hz : z ≠ 0)
    (htrial : inner ℂ
      (z • (if even then v + l2Inversion v else v - l2Inversion v)) u = 0) :
    inner ℂ v u = 0 ∧ inner ℂ (l2Inversion v) u = 0 := by
  have hrel := inner_l2Inversion_of_parity even hu v
  have hzstar : star z ≠ 0 := star_ne_zero.mpr hz
  have hleft : inner ℂ v u = 0 := by
    have hsum : inner ℂ v u + inner ℂ v u = 0 := by
      cases even
      · simp only [Bool.false_eq_true, ↓reduceIte, inner_smul_left, inner_sub_left] at htrial
        simp only [Bool.false_eq_true, ↓reduceIte] at hrel
        rw [hrel, sub_neg_eq_add] at htrial
        exact (mul_eq_zero.mp htrial).resolve_left hzstar
      · simp only [↓reduceIte, inner_smul_left, inner_add_left] at htrial
        simp only [↓reduceIte] at hrel
        rw [hrel] at htrial
        exact (mul_eq_zero.mp htrial).resolve_left hzstar
    have htwo : (2 : ℂ) * inner ℂ v u = 0 := by simpa only [two_mul] using hsum
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  refine ⟨hleft, ?_⟩
  rw [hrel, hleft]
  cases even <;> simp

end InfiniteZero
