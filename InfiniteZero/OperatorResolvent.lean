import InfiniteZero.CoerciveOperator
import Mathlib.Tactic.Module
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Resolvent identities from the actual graph

A bounded map is certified as the inverse of `A - E` through membership
in the graph of the given unbounded operator. Self-adjointness makes this
right inverse a left inverse as well. The exact resolvent identity then
gives norm continuity on every set with a uniform inverse bound.
-/

noncomputable section
open Set
open scoped NNReal

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Actual graph certificate for an inverse of `A - E`. -/
def IsOperatorResolvent (A : H →ₗ.[ℂ] H) (E : ℝ) (R : H →L[ℂ] H) : Prop :=
  ∀ y : H, (R y, y + (E : ℂ) • R y) ∈ A.graph

theorem selfAdjoint_inner_of_mem_graph [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {q r : H × H}
    (hq : q ∈ A.graph) (hr : r ∈ A.graph) :
    inner ℂ q.2 r.1 = inner ℂ q.1 r.2 := by
  obtain ⟨u, hu, hv⟩ := A.mem_graph_iff.mp hq
  obtain ⟨v, hru, hrv⟩ := A.mem_graph_iff.mp hr
  have hstar : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hs : A.IsFormalAdjoint A := by
    simpa only [hstar] using (LinearPMap.adjoint_isFormalAdjoint hA.dense_domain)
  simpa only [hu, hv, hru, hrv] using hs u v

theorem IsOperatorResolvent.eq_zero_of_eigen [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} {E : ℝ} {R : H →L[ℂ] H}
    (hR : IsOperatorResolvent A E R) (hA : IsSelfAdjoint A) {x : H}
    (hx : (x, (E : ℂ) • x) ∈ A.graph) : x = 0 := by
  have h := selfAdjoint_inner_of_mem_graph hA hx (hR x)
  simp only [inner_smul_left, inner_add_right, inner_smul_right,
    Complex.conj_ofReal] at h
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  linear_combination -h

theorem IsOperatorResolvent.left_inverse [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} {E : ℝ} {R : H →L[ℂ] H}
    (hR : IsOperatorResolvent A E R) (hA : IsSelfAdjoint A)
    {q : H × H} (hq : q ∈ A.graph) : R (q.2 - (E : ℂ) • q.1) = q.1 := by
  let y := q.2 - (E : ℂ) • q.1
  have hd := A.graph.sub_mem hq (hR y)
  have heigen : (q.1 - R y, (E : ℂ) • (q.1 - R y)) ∈ A.graph := by
    convert hd using 1
    congr 1
    dsimp [y]
    module
  exact (sub_eq_zero.mp (hR.eq_zero_of_eigen hA heigen)).symm

theorem IsOperatorResolvent.nonneg_of_lower_bound
    {A : H →ₗ.[ℂ] H} {E : ℝ} {R : H →L[ℂ] H}
    (hR : IsOperatorResolvent A E R)
    (hbound : ∀ u : A.domain, E * ‖(u : H)‖ ^ 2 ≤
      (inner ℂ (u : H) (A u)).re) (y : H) :
    0 ≤ (inner ℂ y (R y)).re := by
  obtain ⟨u, hu, hv⟩ := A.mem_graph_iff.mp (hR y)
  have h := hbound u
  rw [hu, hv, inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re] at h
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have hn : (inner ℂ (R y) (R y)).re = ‖R y‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (R y)).symm
  rw [hn] at h
  have hs : (inner ℂ y (R y)).re = (inner ℂ (R y) y).re :=
    inner_re_symm (𝕜 := ℂ) y (R y)
  rw [hs]
  linarith

theorem IsOperatorResolvent.isSelfAdjoint [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} {E : ℝ} {R : H →L[ℂ] H}
    (hR : IsOperatorResolvent A E R) (hA : IsSelfAdjoint A) : IsSelfAdjoint R := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have h := selfAdjoint_inner_of_mem_graph hA (hR x) (hR y)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal] at h
  linear_combination -h

theorem IsOperatorResolvent.identity [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {E F : ℝ}
    {R S : H →L[ℂ] H} (hR : IsOperatorResolvent A E R)
    (hS : IsOperatorResolvent A F S) :
    R - S = ((E - F : ℝ) : ℂ) • R.comp S := by
  ext y
  have h := hR.left_inverse hA (hS y)
  simp only [map_sub, map_add, map_smul] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofReal_sub]
  calc
    R y - S y = R y - (R y + (F : ℂ) • R (S y) - (E : ℂ) • R (S y)) := by rw [h]
    _ = _ := by module

theorem IsOperatorResolvent.norm_sub_le [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {E F : ℝ}
    {R S : H →L[ℂ] H} (hR : IsOperatorResolvent A E R)
    (hS : IsOperatorResolvent A F S) :
    ‖R - S‖ ≤ |E - F| * (‖R‖ * ‖S‖) := by
  rw [hR.identity hA hS, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (R.opNorm_comp_le S) (abs_nonneg _)

theorem operatorResolvent_lipschitzOn [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {s : Set ℝ}
    (R : ℝ → H →L[ℂ] H) {C : ℝ≥0}
    (hR : ∀ E ∈ s, IsOperatorResolvent A E (R E))
    (hbound : ∀ E ∈ s, ‖R E‖ ≤ C) :
    LipschitzOnWith (C * C) R s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro E hE F hF
  rw [dist_eq_norm, Real.dist_eq]
  have hn := (hR E hE).norm_sub_le hA (hR F hF)
  have hp := mul_le_mul (hbound E hE) (hbound F hF) (norm_nonneg _) C.coe_nonneg
  calc
    ‖R E - R F‖ ≤ |E - F| * (‖R E‖ * ‖R F‖) := hn
    _ ≤ |E - F| * ((C : ℝ) * C) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ = _ := by simp only [NNReal.coe_mul]; ring

theorem operatorResolvent_continuousOn [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {s : Set ℝ}
    (R : ℝ → H →L[ℂ] H) {C : ℝ≥0}
    (hR : ∀ E ∈ s, IsOperatorResolvent A E (R E))
    (hbound : ∀ E ∈ s, ‖R E‖ ≤ C) : ContinuousOn R s :=
  (operatorResolvent_lipschitzOn hA R hR hbound).continuousOn

end InfiniteZero
