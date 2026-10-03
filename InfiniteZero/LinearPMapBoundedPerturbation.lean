import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Bounded perturbations of unbounded self-adjoint operators

The sum below keeps the original domain definitionally. Continuity of the
bounded summand preserves the adjoint domain, and density identifies the
adjoint as the sum of the two adjoints. Self-adjointness follows directly.
-/

noncomputable section
open Set
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Add a bounded operator without changing the domain of the unbounded one. -/
def operatorAddBounded (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := A.domain
  toFun := A.toFun + B.toLinearMap.comp A.domain.subtype

@[simp] theorem operatorAddBounded_domain (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) :
    (operatorAddBounded A B).domain = A.domain := rfl

@[simp] theorem operatorAddBounded_apply (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (u : A.domain) : operatorAddBounded A B u = A u + B (u : H) := rfl

/-- Exact graph membership, with the bounded correction removed from the output. -/
theorem mem_graph_operatorAddBounded_iff (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (u v : H) :
    (u, v) ∈ (operatorAddBounded A B).graph ↔ (u, v - B u) ∈ A.graph := by
  simp only [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hv⟩
    refine ⟨x, hx, ?_⟩
    change A x + B (x : H) = v at hv
    rw [← hv, ← hx, add_sub_cancel_right]
  · rintro ⟨x, hx, hv⟩
    refine ⟨x, hx, ?_⟩
    change A x + B (x : H) = v
    rw [hv, hx, sub_add_cancel]

theorem operatorAddBounded_graph (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) :
    ((operatorAddBounded A B).graph : Set (H × H)) =
      (fun q : H × H => (q.1, q.2 + B q.1)) '' (A.graph : Set (H × H)) := by
  ext q
  constructor
  · intro hq
    refine ⟨(q.1, q.2 - B q.1),
      (mem_graph_operatorAddBounded_iff A B q.1 q.2).mp hq, ?_⟩
    simp only [sub_add_cancel]
  · rintro ⟨q, hq, rfl⟩
    apply (mem_graph_operatorAddBounded_iff A B q.1 (q.2 + B q.1)).mpr
    simpa only [add_sub_cancel_right] using hq

variable [CompleteSpace H]

/-- The adjoint domain is unchanged even before density is assumed. -/
theorem operatorAddBounded_adjoint_domain (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) :
    (operatorAddBounded A B).adjoint.domain = A.adjoint.domain := by
  ext y
  rw [LinearPMap.mem_adjoint_domain_iff, LinearPMap.mem_adjoint_domain_iff]
  change Continuous (fun x : A.domain => inner ℂ y (A x + B (x : H))) ↔
    Continuous (fun x : A.domain => inner ℂ y (A x))
  have hB : Continuous (fun x : A.domain => inner ℂ y (B (x : H))) :=
    continuous_const.inner (B.continuous.comp continuous_subtype_val)
  constructor
  · intro h
    have hs := h.sub hB
    simpa only [inner_add_right, add_sub_cancel_right] using hs
  · intro h
    simpa only [inner_add_right] using h.add hB

/-- The genuine adjoint of a densely defined operator plus a bounded operator. -/
theorem operatorAddBounded_adjoint (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hA : Dense (A.domain : Set H)) :
    (operatorAddBounded A B).adjoint = operatorAddBounded A.adjoint B.adjoint := by
  refine LinearPMap.ext (f := (operatorAddBounded A B).adjoint)
    (g := operatorAddBounded A.adjoint B.adjoint) (operatorAddBounded_adjoint_domain A B) ?_
  intro x hx hy
  change (operatorAddBounded A B).adjoint ⟨x, hx⟩ =
    A.adjoint ⟨x, hy⟩ + B.adjoint x
  apply LinearPMap.adjoint_apply_eq (T := operatorAddBounded A B) hA
  intro u
  change inner ℂ (A.adjoint ⟨x, hy⟩ + B.adjoint x) (u : H) =
    inner ℂ x (A u + B (u : H))
  rw [inner_add_left, inner_add_right,
    LinearPMap.adjoint_isFormalAdjoint hA ⟨x, hy⟩ u, B.adjoint_inner_left]

/-- A bounded self-adjoint perturbation preserves self-adjointness on the original domain. -/
theorem isSelfAdjoint_operatorAddBounded (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (operatorAddBounded A B) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  rw [operatorAddBounded_adjoint A B hA.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp hA]
  change B.adjoint = B at hB
  rw [hB]

end InfiniteZero
