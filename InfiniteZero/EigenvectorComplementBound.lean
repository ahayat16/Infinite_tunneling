import InfiniteZero.EigenvectorEnergy

/-!
# The absolute complement floor is preserved by a low eigenvector

If a codimension-one trial complement has energy at least `C`, any nonzero
eigenvector with energy below `C` has that same absolute lower bound on its
own complement. Subtracting its multiple removes the trial overlap,
increases the norm, and preserves the shifted energy.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem eigenvector_complement_lower_of_trial_complement
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (φ : H) {E C : ℝ}
    (hEC : E < C) (w : A.domain) (hw0 : (w : H) ≠ 0)
    (hw : A w = (E : ℂ) • (w : H))
    (hbound : ∀ u : A.domain, inner ℂ φ (u : H) = 0 →
      C * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re)
    (u : A.domain) (hu : inner ℂ (w : H) (u : H) = 0) :
    C * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re := by
  have he : (inner ℂ (w : H) (A w)).re = E * ‖(w : H)‖ ^ 2 := by
    rw [hw, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [show (inner ℂ (w : H) (w : H)).re = ‖(w : H)‖ ^ 2 from
      inner_self_eq_norm_sq (𝕜 := ℂ) (w : H)]
    ring
  have hφw : inner ℂ φ (w : H) ≠ 0 := by
    intro hz
    have h := hbound w hz
    rw [he] at h
    have hCE := (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hw0))).mp h
    exact (not_le_of_gt hEC) hCE
  let a := inner ℂ φ (u : H) / inner ℂ φ (w : H)
  let ξ : A.domain := u - a • w
  have hξorth : inner ℂ φ (ξ : H) = 0 := by
    change inner ℂ φ ((u : H) - a • (w : H)) = 0
    rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hφw, sub_self]
  have hnorm : ‖(u : H)‖ ^ 2 ≤ ‖(ξ : H)‖ ^ 2 := by
    change ‖(u : H)‖ ^ 2 ≤ ‖(u : H) - a • (w : H)‖ ^ 2
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, (inner_eq_zero_symm.mp hu),
      mul_zero, map_zero]
    nlinarith only [sq_nonneg ‖a • (w : H)‖]
  have hlower := hbound ξ hξorth
  have henergy := eigenvector_shiftedEnergy_sub A hA w hw u a
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr hEC.le)
  change (inner ℂ (u : H) (A u)).re - E * ‖(u : H)‖ ^ 2 =
    (inner ℂ (ξ : H) (A ξ)).re - E * ‖(ξ : H)‖ ^ 2 at henergy
  nlinarith only [hlower, henergy, hnorm']

end InfiniteZero
