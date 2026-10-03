import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Self-adjoint restriction to a reducing closed subspace

The assumption is invariance of the actual operator graph under the
orthogonal projection in both coordinates. The restriction inherits its
domain from the original operator and its value is the original operator's
value, with membership in the subspace proved from graph uniqueness.
-/

noncomputable section
open Set

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def reducingDomain (A : H →ₗ.[ℂ] H) (K : Submodule ℂ H) : Submodule ℂ K :=
  A.domain.comap K.subtype

def reducingDomainInclusion (A : H →ₗ.[ℂ] H) (K : Submodule ℂ H) :
    reducingDomain A K →ₗ[ℂ] A.domain where
  toFun x := ⟨((x : K) : H), x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (A : H →ₗ.[ℂ] H) (K : Submodule ℂ H) [CompleteSpace K]

theorem reducingProjection_mem_domain
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    {x : H} (hx : x ∈ A.domain) : K.starProjection x ∈ A.domain := by
  obtain ⟨y, hy, _⟩ := A.mem_graph_iff.mp
    (hP _ (A.mem_graph ⟨x, hx⟩))
  change (y : H) = K.starProjection x at hy
  rw [← hy]
  exact y.property

theorem reducing_apply_mem
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    (x : A.domain) (hx : (x : H) ∈ K) : A x ∈ K := by
  apply K.starProjection_eq_self_iff.mp
  exact A.mem_graph_snd_inj (hP _ (A.mem_graph x)) (A.mem_graph x)
    (K.starProjection_eq_self_iff.mpr hx)

/-- The genuine restriction, not just a projected value on an arbitrary domain. -/
def reducingRestriction
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph) :
    K →ₗ.[ℂ] K where
  domain := reducingDomain A K
  toFun := (A.toFun.comp (reducingDomainInclusion A K)).codRestrict K
    (fun x => reducing_apply_mem A K hP (reducingDomainInclusion A K x) (x : K).property)

@[simp] theorem reducingRestriction_domain
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph) :
    (reducingRestriction A K hP).domain = reducingDomain A K := rfl

@[simp] theorem reducingRestriction_apply_coe
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    (x : (reducingRestriction A K hP).domain) :
    (reducingRestriction A K hP x : H) = A (reducingDomainInclusion A K x) := rfl

def reducingDomainProjection
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph) :
    A.domain →L[ℂ] reducingDomain A K :=
  (K.orthogonalProjection.comp A.domain.subtypeL).codRestrict (reducingDomain A K)
    (fun x => reducingProjection_mem_domain A K hP x.property)

theorem reducingRestriction_projected
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    (x : A.domain) :
    reducingRestriction A K hP (reducingDomainProjection A K hP x) =
      K.orthogonalProjection (A x) := by
  apply Subtype.ext
  exact A.mem_graph_snd_inj
    (A.mem_graph (reducingDomainInclusion A K (reducingDomainProjection A K hP x)))
    (hP _ (A.mem_graph x)) rfl

theorem reducingRestriction_dense_domain
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    (hA : Dense (A.domain : Set H)) :
    Dense ((reducingRestriction A K hP).domain : Set K) := by
  have hsurj : Function.Surjective K.orthogonalProjection := fun x =>
    ⟨(x : H), Submodule.orthogonalProjection_mem_subspace_eq_self x⟩
  apply hsurj.denseRange.dense_of_mapsTo K.orthogonalProjection.continuous hA
  intro x hx
  exact reducingProjection_mem_domain A K hP hx

theorem reducingRestriction_isFormalAdjoint
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    (hA : A.IsFormalAdjoint A) :
    (reducingRestriction A K hP).IsFormalAdjoint (reducingRestriction A K hP) := by
  intro x y
  exact hA (reducingDomainInclusion A K x) (reducingDomainInclusion A K y)

variable [CompleteSpace H]

theorem reducingRestriction_adjoint_domain_subset
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    {y : K} (hy : y ∈ (reducingRestriction A K hP).adjoint.domain) :
    (y : H) ∈ A.adjoint.domain := by
  let B := reducingRestriction A K hP
  have hyC : Continuous (fun x : B.domain => inner ℂ y (B x)) :=
    (B.mem_adjoint_domain_iff y).mp hy
  have hcont : Continuous (fun x : A.domain =>
      inner ℂ y (B (reducingDomainProjection A K hP x))) :=
    hyC.comp (reducingDomainProjection A K hP).continuous
  rw [A.mem_adjoint_domain_iff]
  change Continuous (fun x : A.domain => inner ℂ (y : H) (A x))
  convert hcont using 1
  funext x
  change inner ℂ (y : H) (A x) =
    inner ℂ y (reducingRestriction A K hP (reducingDomainProjection A K hP x))
  rw [reducingRestriction_projected,
    Submodule.inner_orthogonalProjection_eq_of_mem_left]

theorem isSelfAdjoint_reducingRestriction
    (hP : ∀ q ∈ A.graph, (K.starProjection q.1, K.starProjection q.2) ∈ A.graph)
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (reducingRestriction A K hP) := by
  have hstar : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hsym : A.IsFormalAdjoint A := by
    simpa only [hstar] using LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  have hdense := reducingRestriction_dense_domain A K hP hA.dense_domain
  have hle := (reducingRestriction_isFormalAdjoint A K hP hsym).le_adjoint hdense
  have hdom : (reducingRestriction A K hP).domain =
      (reducingRestriction A K hP).adjoint.domain := by
    apply le_antisymm hle.1
    intro y hy
    have hyA := reducingRestriction_adjoint_domain_subset A K hP hy
    rw [hstar] at hyA
    exact hyA
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hle hdom).symm

end InfiniteZero
