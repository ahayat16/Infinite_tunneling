import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Elementary inversion facts for coercive unbounded operators

These general Hilbert-space arguments use the genuine closed graph and
adjoint. They provide functional analysis needed by the atomic Schur step,
without any assumption about the potential or tunneling.
-/

noncomputable section
open Set
open scoped ComplexConjugate NNReal

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem coerciveOperator_norm_lower (A : H →ₗ.[ℂ] H) {g : ℝ}
    (hbound : ∀ u : A.domain, g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re)
    (u : A.domain) : g * ‖(u : H)‖ ≤ ‖A u‖ := by
  by_cases hu : ‖(u : H)‖ = 0
  · simp [hu]
  have hp : 0 < ‖(u : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hinner : (inner ℂ (u : H) (A u)).re ≤ ‖(u : H)‖ * ‖A u‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [hbound u]

theorem coerciveOperator_injective (A : H →ₗ.[ℂ] H) {g : ℝ} (hg : 0 < g)
    (hbound : ∀ u : A.domain, g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    Function.Injective A := by
  apply (injective_iff_map_eq_zero A.toFun).mpr
  intro u hu
  change A u = 0 at hu
  apply Subtype.ext
  have h := coerciveOperator_norm_lower A hbound u
  rw [hu, norm_zero] at h
  have hn : ‖(u : H)‖ = 0 := by nlinarith [norm_nonneg (u : H)]
  exact norm_eq_zero.mp hn

theorem coerciveOperator_isClosed_range [CompleteSpace H] (A : H →ₗ.[ℂ] H)
    (hclosed : A.IsClosed) {g : ℝ} (hg : 0 < g)
    (hbound : ∀ u : A.domain, g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    IsClosed (Set.range A) := by
  letI : CompleteSpace A.graph := hclosed.completeSpace_coe
  let F : A.graph →L[ℂ] H := (ContinuousLinearMap.snd ℂ H H).comp A.graph.subtypeL
  let K : ℝ≥0 := ⟨max 1 g⁻¹, le_trans zero_le_one (le_max_left _ _)⟩
  have hanti : AntilipschitzWith K F := F.antilipschitz_of_bound fun q => by
    obtain ⟨u, hu, hv⟩ := (A.mem_graph_iff).mp q.property
    have h := coerciveOperator_norm_lower A hbound u
    have hfirst : ‖(q : H × H).1‖ ≤ g⁻¹ * ‖(q : H × H).2‖ := by
      rw [← hu, ← hv]
      exact (le_inv_mul_iff₀ hg).mpr h
    change max ‖(q : H × H).1‖ ‖(q : H × H).2‖ ≤
      max 1 g⁻¹ * ‖(q : H × H).2‖
    apply max_le
    · exact hfirst.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    · simpa using mul_le_mul_of_nonneg_right (le_max_left 1 g⁻¹) (norm_nonneg (q : H × H).2)
  have heq : Set.range F = Set.range A := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨u, _, hu⟩ := (A.mem_graph_iff).mp q.property
      exact ⟨u, hu⟩
    · rintro ⟨u, rfl⟩
      exact ⟨⟨((u : H), A u), A.mem_graph u⟩, rfl⟩
  rw [← heq]
  exact hanti.isClosed_range F.uniformContinuous

theorem coerciveSelfAdjoint_surjective [CompleteSpace H] (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {g : ℝ} (hg : 0 < g)
    (hbound : ∀ u : A.domain, g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    Function.Surjective A := by
  let R : Submodule ℂ H := LinearMap.range A.toFun
  have hclosed : IsClosed (R : Set H) :=
    coerciveOperator_isClosed_range A hA.isClosed hg hbound
  letI : CompleteSpace R := hclosed.completeSpace_coe
  have hstar : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hperp : Rᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have horth : ∀ u : A.domain, inner ℂ x (A u) = 0 := fun u =>
      (R.mem_orthogonal' x).mp hx (A u) ⟨u, rfl⟩
    have hdom : x ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists x ⟨0, fun u => by simp [horth u]⟩
    have hzero : A.adjoint ⟨x, hdom⟩ = 0 :=
      LinearPMap.adjoint_apply_eq hA.dense_domain _ (fun u => by simp [horth u])
    have hgraph := A.adjoint.mem_graph ⟨x, hdom⟩
    rw [hzero] at hgraph
    change (x, 0) ∈ A.adjoint.graph at hgraph
    rw [hstar] at hgraph
    obtain ⟨u, hu, hv⟩ := A.mem_graph_iff.mp hgraph
    have huzero : u = 0 := coerciveOperator_injective A hg hbound (by simpa using hv)
    change x = 0
    exact hu.symm.trans (congrArg Subtype.val huzero)
  have htop : R = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  intro y
  have hy : y ∈ R := by rw [htop]; trivial
  exact hy

/-- A positive coercive self-adjoint operator has a bounded everywhere-defined
inverse, with its graph identity and the quantitative norm bound. -/
theorem exists_coerciveSelfAdjoint_inverse [CompleteSpace H] (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {g : ℝ} (hg : 0 < g)
    (hbound : ∀ u : A.domain, g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ g⁻¹ ∧ ∀ y : H, (R y, y) ∈ A.graph := by
  let e : A.domain ≃ₗ[ℂ] H := LinearEquiv.ofBijective A.toFun
    ⟨coerciveOperator_injective A hg hbound, coerciveSelfAdjoint_surjective A hA hg hbound⟩
  let r : H →ₗ[ℂ] H := A.domain.subtype.comp e.symm.toLinearMap
  have hr (y : H) : ‖r y‖ ≤ g⁻¹ * ‖y‖ := by
    have h := coerciveOperator_norm_lower A hbound (e.symm y)
    have he : A (e.symm y) = y := e.apply_symm_apply y
    rw [he] at h
    exact (le_inv_mul_iff₀ hg).mpr h
  let R : H →L[ℂ] H := r.mkContinuous g⁻¹ hr
  refine ⟨R, R.opNorm_le_bound (inv_nonneg.mpr hg.le) hr, ?_⟩
  intro y
  have hgraph := A.mem_graph (e.symm y)
  have he : A (e.symm y) = y := e.apply_symm_apply y
  simpa only [he] using hgraph

/-- Positivity of the inverse is obtained directly from its graph identity. -/
theorem coerciveOperator_inverse_nonneg (A : H →ₗ.[ℂ] H) {g : ℝ} (hg : 0 ≤ g)
    (hbound : ∀ u : A.domain, g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re)
    (R : H →L[ℂ] H) (hR : ∀ y : H, (R y, y) ∈ A.graph) (y : H) :
    0 ≤ (inner ℂ y (R y)).re := by
  obtain ⟨u, hu, hv⟩ := A.mem_graph_iff.mp (hR y)
  have h := (mul_nonneg hg (sq_nonneg ‖(u : H)‖)).trans (hbound u)
  rw [hu, hv] at h
  have hsymm : (inner ℂ y (R y)).re = (inner ℂ (R y) y).re :=
    inner_re_symm (𝕜 := ℂ) y (R y)
  rwa [hsymm]

theorem selfAdjoint_operatorInverse [CompleteSpace H] (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (R : H →L[ℂ] H)
    (hR : ∀ y : H, (R y, y) ∈ A.graph) : IsSelfAdjoint R := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  obtain ⟨u, hu, hv⟩ := A.mem_graph_iff.mp (hR x)
  obtain ⟨v, hvu, hvv⟩ := A.mem_graph_iff.mp (hR y)
  have hstar : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hsymm : A.IsFormalAdjoint A := by
    simpa only [hstar] using (LinearPMap.adjoint_isFormalAdjoint hA.dense_domain)
  have h := hsymm u v
  rw [hu, hv, hvu, hvv] at h
  exact h.symm

end InfiniteZero
