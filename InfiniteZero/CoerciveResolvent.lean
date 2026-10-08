import InfiniteZero.CoerciveOperator
import InfiniteZero.OperatorResolvent
import InfiniteZero.LinearPMapBoundedPerturbation

/-!
# Uniform real resolvents below a coercive threshold

A self-adjoint operator bounded below by `E₀ + g`, with `g > 0`, has a
resolvent at every real `E ≤ E₀`. The inverse norm is uniformly at most
`g⁻¹`, and a family of these actual graph inverses is norm-continuous.
-/

noncomputable section
open Set
open scoped NNReal
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Subtract a real spectral parameter on the unchanged operator domain. -/
def shiftedOperator (A : H →ₗ.[ℂ] H) (E : ℝ) : H →ₗ.[ℂ] H :=
  operatorAddBounded A (-(E : ℂ) • ContinuousLinearMap.id ℂ H)

@[simp] theorem shiftedOperator_domain (A : H →ₗ.[ℂ] H) (E : ℝ) :
    (shiftedOperator A E).domain = A.domain := rfl

@[simp] theorem shiftedOperator_apply (A : H →ₗ.[ℂ] H) (E : ℝ) (u : A.domain) :
    shiftedOperator A E u = A u - (E : ℂ) • (u : H) := by
  change A u + (-(E : ℂ)) • (u : H) = A u - (E : ℂ) • (u : H)
  rw [neg_smul, sub_eq_add_neg]

theorem mem_graph_shiftedOperator_iff (A : H →ₗ.[ℂ] H) (E : ℝ) (u v : H) :
    (u, v) ∈ (shiftedOperator A E).graph ↔ (u, v + (E : ℂ) • u) ∈ A.graph := by
  simpa only [shiftedOperator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    neg_smul, ContinuousLinearMap.neg_apply, sub_neg_eq_add] using
    mem_graph_operatorAddBounded_iff A (-(E : ℂ) • ContinuousLinearMap.id ℂ H) u v

variable [CompleteSpace H]

theorem isSelfAdjoint_shiftedOperator (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (E : ℝ) :
    IsSelfAdjoint (shiftedOperator A E) := by
  apply isSelfAdjoint_operatorAddBounded A _ hA
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ ((-(E : ℂ)) • x) y = inner ℂ x ((-(E : ℂ)) • y)
  simp only [inner_smul_left, inner_smul_right, map_neg, Complex.conj_ofReal]

omit [CompleteSpace H] in
theorem shiftedOperator_coercive (A : H →ₗ.[ℂ] H) {E₀ g E : ℝ}
    (hbound : ∀ u : A.domain, (E₀ + g) * ‖(u : H)‖ ^ 2 ≤
      (inner ℂ (u : H) (A u)).re) (hE : E ≤ E₀)
    (u : (shiftedOperator A E).domain) :
    g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (shiftedOperator A E u)).re := by
  rw [shiftedOperator_apply, inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hn : (inner ℂ (u : H) (u : H)).re = ‖(u : H)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (u : H)).symm
  rw [hn]
  have he := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖(u : H)‖)
  nlinarith only [hbound u, he]

/-- Existence of a genuine resolvent with a bound independent of the real parameter. -/
theorem exists_coerciveSelfAdjoint_resolvent (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {E₀ g : ℝ} (hg : 0 < g)
    (hbound : ∀ u : A.domain, (E₀ + g) * ‖(u : H)‖ ^ 2 ≤
      (inner ℂ (u : H) (A u)).re) (E : ℝ) (hE : E ≤ E₀) :
    ∃ R : H →L[ℂ] H, IsOperatorResolvent A E R ∧ ‖R‖ ≤ g⁻¹ := by
  obtain ⟨R, hn, hR⟩ := exists_coerciveSelfAdjoint_inverse (shiftedOperator A E)
    (isSelfAdjoint_shiftedOperator A hA E) hg (shiftedOperator_coercive A hbound hE)
  refine ⟨R, ?_, hn⟩
  exact fun y => (mem_graph_shiftedOperator_iff A E (R y) y).mp (hR y)

/-- A single family is chosen before the energy parameter and certified on the
entire half-line. No resolvent assertion is made outside that half-line. -/
theorem exists_coerciveSelfAdjoint_resolventFamily (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {E₀ g : ℝ} (hg : 0 < g)
    (hbound : ∀ u : A.domain, (E₀ + g) * ‖(u : H)‖ ^ 2 ≤
      (inner ℂ (u : H) (A u)).re) :
    ∃ R : ℝ → H →L[ℂ] H,
      (∀ E ≤ E₀, IsOperatorResolvent A E (R E) ∧ ‖R E‖ ≤ g⁻¹) ∧
      ContinuousOn R (Iic E₀) := by
  classical
  have hex : ∀ E : ℝ, ∃ R : H →L[ℂ] H,
      E ≤ E₀ → IsOperatorResolvent A E R ∧ ‖R‖ ≤ g⁻¹ := by
    intro E
    by_cases hE : E ≤ E₀
    · obtain ⟨R, hR, hn⟩ := exists_coerciveSelfAdjoint_resolvent A hA hg hbound E hE
      exact ⟨R, fun _ => ⟨hR, hn⟩⟩
    · exact ⟨0, fun h => (hE h).elim⟩
  choose R hR using hex
  refine ⟨R, hR, ?_⟩
  exact operatorResolvent_continuousOn hA R (C := ⟨g⁻¹, inv_nonneg.mpr hg.le⟩)
    (fun E hE => (hR E hE).1) (fun E hE => (hR E hE).2)

end InfiniteZero
