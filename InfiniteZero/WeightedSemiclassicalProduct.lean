import InfiniteZero.SemiclassicalLeibniz

/-!
# Weighted semiclassical Leibniz estimates

A scalar coefficient with fixed derivative bounds can multiply a wavefunction
whose semiclassical jets have one common weighted bound. The weight is a
nonnegative number at the evaluation point, so no derivative of it occurs.
For scales in `[0,1]`, the remaining semiclassical factors on the coefficient
can be discarded. A finite sum then gives a constant for all orders up to a
prescribed maximum, chosen before the functions and evaluation parameters.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The weight is multiplied after differentiation. The binomial sum keeps
the individual coefficient bounds, and the statement includes zero scale. -/
theorem weighted_semiclassical_norm_iteratedFDeriv_smul_le_of_bounds
    {q : E → ℝ} {u : E → F} (hq : ContDiff ℝ ∞ q) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (x : E) (A : ℕ → ℝ) (hA : ∀ i ≤ n, 0 ≤ A i)
    {h w L M : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hw : 0 ≤ w) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hqbound : ∀ i ≤ n, ‖iteratedFDeriv ℝ i q x‖ ≤ A i * L)
    (hubound : ∀ k ≤ n, w * h ^ k * ‖iteratedFDeriv ℝ k u x‖ ≤ M) :
    w * h ^ n * ‖iteratedFDeriv ℝ n (fun y => q y • u y) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i) * L * M := by
  have hqscaled (i : ℕ) (hi : i ≤ n) :
      h ^ i * ‖iteratedFDeriv ℝ i q x‖ ≤ A i * L := by
    calc
      _ ≤ h ^ i * (A i * L) :=
        mul_le_mul_of_nonneg_left (hqbound i hi) (pow_nonneg hh i)
      _ ≤ 1 * (A i * L) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hh hh1) (mul_nonneg (hA i hi) hL)
      _ = A i * L := one_mul _
  calc
    _ = w * (h ^ n * ‖iteratedFDeriv ℝ n (fun y => q y • u y) x‖) := by ring
    _ ≤ w * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (h ^ i * ‖iteratedFDeriv ℝ i q x‖) *
        (h ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) u x‖)) :=
      mul_le_mul_of_nonneg_left (semiclassical_norm_iteratedFDeriv_smul_le hh hq hu n x) hw
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (h ^ i * ‖iteratedFDeriv ℝ i q x‖) *
        (w * h ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) u x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (A i * L) * M := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      calc
        _ ≤ (n.choose i : ℝ) * (h ^ i * ‖iteratedFDeriv ℝ i q x‖) * M :=
          mul_le_mul_of_nonneg_left (hubound (n - i) (Nat.sub_le _ _)) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hqscaled i hin) (Nat.cast_nonneg _)) hM
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- One positive constant works through a fixed order. It depends only on
the prescribed scalar jet bounds and the maximal order, before the choice
of either function, scale, point, weight or envelopes. -/
theorem exists_weighted_semiclassical_smul_bound_upTo
    (n : ℕ) (A : ℕ → ℝ) (hA : ∀ i ≤ n, 0 ≤ A i) :
    ∃ C > 0, ∀ (q : E → ℝ) (u : E → F),
      ContDiff ℝ ∞ q → ContDiff ℝ ∞ u → ∀ x : E,
      ∀ h w L M : ℝ, 0 ≤ h → h ≤ 1 → 0 ≤ w → 0 ≤ L → 0 ≤ M →
      (∀ i ≤ n, ‖iteratedFDeriv ℝ i q x‖ ≤ A i * L) →
      (∀ k ≤ n, w * h ^ k * ‖iteratedFDeriv ℝ k u x‖ ≤ M) →
      ∀ j : ℕ, j ≤ n →
        w * h ^ j * ‖iteratedFDeriv ℝ j (fun y => q y • u y) x‖ ≤ C * L * M := by
  let S (j : ℕ) : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i
  have hS (j : ℕ) (hj : j ≤ n) : 0 ≤ S j := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (Nat.cast_nonneg _)
      (hA i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj))
  let C : ℝ := (∑ j ∈ Finset.range (n + 1), S j) + 1
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), S j :=
    Finset.sum_nonneg fun j hj => hS j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro q u hq hu x h w L M hh hh1 hw hL hM hqbound hubound j hj
  have hSj : S j ≤ C := by
    have hs := Finset.single_le_sum
      (fun k hk => hS k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      (show j ∈ Finset.range (n + 1) from Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    dsimp [C]
    linarith
  exact (weighted_semiclassical_norm_iteratedFDeriv_smul_le_of_bounds hq hu j x A
    (fun i hi => hA i (hi.trans hj)) hh hh1 hw hL hM
    (fun i hi => hqbound i (hi.trans hj))
    (fun k hk => hubound k (hk.trans hj))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSj hL) hM)

end InfiniteZero
