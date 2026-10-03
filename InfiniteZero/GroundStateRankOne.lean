import InfiniteZero.GroundStateCertificate
import InfiniteZero.EigenvectorEnergy
import InfiniteZero.OrthogonalSchurGeometry

/-!
# The exact rank-one lower bound from a ground-state certificate

Orthogonal projection preserves the actual operator domain. Subtracting
the normalized certified eigenvector leaves the shifted quadratic energy
unchanged, so the complement gap gives the full rank-one bound without
any loss in its constant.
-/

noncomputable section
namespace InfiniteZero
namespace GroundStateCertificate

variable {A : L2Space →ₗ.[ℂ] L2Space} {E : ℝ}

/-- A certified gap implies the full rank-one form bound, with no loss in its constant. -/
theorem rankOne_lower_bound (h : GroundStateCertificate A E)
    (hA : IsSelfAdjoint A) (u : A.domain) :
    h.gap * (‖(u : L2Space)‖ ^ 2 -
      ‖inner ℂ (h.normalizedVector : L2Space) (u : L2Space)‖ ^ 2) ≤
      (inner ℂ (u : L2Space) (A u)).re - E * ‖(u : L2Space)‖ ^ 2 := by
  let w : A.domain := h.normalizedVector
  let a : ℂ := inner ℂ (w : L2Space) (u : L2Space)
  let z : A.domain := u - a • w
  have hw : ‖(w : L2Space)‖ = 1 := h.normalizedVector_norm
  have hww : inner ℂ (w : L2Space) (w : L2Space) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    norm_num
  have hz : inner ℂ (w : L2Space) (z : L2Space) = 0 := by
    change inner ℂ (w : L2Space) ((u : L2Space) - a • (w : L2Space)) = 0
    rw [inner_sub_right, inner_smul_right, hww, mul_one]
    exact sub_self _
  have hvector : (h.vector : L2Space) =
      (‖(h.vector : L2Space)‖ : ℂ) • (w : L2Space) := by
    have hn : ‖(h.vector : L2Space)‖ ≠ 0 := norm_ne_zero_iff.mpr h.vector_ne_zero
    simp only [w, normalizedVector, Submodule.coe_smul, smul_smul,
      ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_smul]
  have hzorig : inner ℂ (h.vector : L2Space) (z : L2Space) = 0 := by
    rw [hvector, inner_smul_left, hz, mul_zero]
  let η : orthogonalComplement (w : L2Space) :=
    ⟨(z : L2Space), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hz⟩
  have hdecomp : a • (w : L2Space) + (η : L2Space) = (u : L2Space) := by
    change a • (w : L2Space) + ((u : L2Space) - a • (w : L2Space)) = _
    abel
  have hnorm : ‖(u : L2Space)‖ ^ 2 = ‖a‖ ^ 2 + ‖(z : L2Space)‖ ^ 2 := by
    have hn := schur_decomposition_norm_sq (w : L2Space) hw a η
    rw [hdecomp] at hn
    exact hn
  have hgap := h.gap_bound z hzorig
  have henergy := eigenvector_shiftedEnergy_sub A hA w
    h.normalizedVector_eigenvector u a
  change (inner ℂ (u : L2Space) (A u)).re - E * ‖(u : L2Space)‖ ^ 2 =
    (inner ℂ (z : L2Space) (A z)).re - E * ‖(z : L2Space)‖ ^ 2 at henergy
  change h.gap * (‖(u : L2Space)‖ ^ 2 - ‖a‖ ^ 2) ≤ _
  rw [show ‖(u : L2Space)‖ ^ 2 - ‖a‖ ^ 2 = ‖(z : L2Space)‖ ^ 2 by linarith only [hnorm], henergy]
  nlinarith only [hgap]

end GroundStateCertificate
end InfiniteZero
