import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Compression of a self-adjoint operator off a domain vector

The compression acts on the actual orthogonal complement, with the domain
inherited from the original operator. A unit vector in the original domain
ensures that orthogonal projection preserves that domain. Self-adjointness is
proved directly from the adjoint domain, without assuming that the vector is
an eigenvector or that the orthogonal complement is invariant under the operator.
-/

noncomputable section

open Set
open scoped ComplexConjugate

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hilbert subspace orthogonal to a specified vector. -/
abbrev orthogonalComplement (φ : H) : Submodule ℂ H := (Submodule.span ℂ {φ})ᗮ

/-- The genuine orthogonal projection, with codomain the orthogonal complement. -/
abbrev complementProjection (φ : H) : H →L[ℂ] orthogonalComplement φ :=
  (orthogonalComplement φ).orthogonalProjection

theorem complementProjection_coe (φ : H) (hφ : ‖φ‖ = 1) (x : H) :
    (complementProjection φ x : H) = x - inner ℂ φ x • φ := by
  change (Submodule.span ℂ {φ})ᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℂ hφ]

@[simp] theorem complementProjection_subtype (φ : H) (x : orthogonalComplement φ) :
    complementProjection φ (x : H) = x :=
  Submodule.orthogonalProjection_mem_subspace_eq_self x

theorem complementProjection_surjective (φ : H) :
    Function.Surjective (complementProjection φ) := fun x =>
  ⟨(x : H), complementProjection_subtype φ x⟩

/-- The operator domain inherited inside the orthogonal Hilbert subspace. -/
def compressionDomain (A : H →ₗ.[ℂ] H) (φ : H) : Submodule ℂ (orthogonalComplement φ) :=
  A.domain.comap (orthogonalComplement φ).subtype

/-- Inclusion of the compression domain into the original operator domain. -/
def compressionDomainInclusion (A : H →ₗ.[ℂ] H) (φ : H) :
    compressionDomain A φ →ₗ[ℂ] A.domain where
  toFun x := ⟨(x : orthogonalComplement φ), x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compression of `A` to the orthogonal complement, with its actual domain. -/
def orthogonalCompression (A : H →ₗ.[ℂ] H) (φ : H) :
    orthogonalComplement φ →ₗ.[ℂ] orthogonalComplement φ where
  domain := compressionDomain A φ
  toFun := (complementProjection φ).toLinearMap.comp
    (A.toFun.comp (compressionDomainInclusion A φ))

@[simp] theorem orthogonalCompression_domain (A : H →ₗ.[ℂ] H) (φ : H) :
    (orthogonalCompression A φ).domain = compressionDomain A φ := rfl

@[simp] theorem orthogonalCompression_apply (A : H →ₗ.[ℂ] H) (φ : H)
    (x : (orthogonalCompression A φ).domain) :
    orthogonalCompression A φ x =
      complementProjection φ (A (compressionDomainInclusion A φ x)) := rfl

theorem complementProjection_mem_domain (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) {x : H} (hx : x ∈ A.domain) :
    (complementProjection (φ : H) x : H) ∈ A.domain := by
  rw [complementProjection_coe (φ : H) hφ]
  exact A.domain.sub_mem hx (A.domain.smul_mem _ φ.property)

/-- The projection is continuous also between the domains with their ambient norms. -/
def compressionDomainProjection (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) : A.domain →L[ℂ] compressionDomain A (φ : H) :=
  ((complementProjection (φ : H)).comp A.domain.subtypeL).codRestrict
    (compressionDomain A (φ : H)) (fun x =>
      complementProjection_mem_domain A φ hφ x.property)

theorem compressionDomainInclusion_projection (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (x : A.domain) :
    compressionDomainInclusion A (φ : H) (compressionDomainProjection A φ hφ x) =
      x - inner ℂ (φ : H) (x : H) • φ := by
  apply Subtype.ext
  exact complementProjection_coe (φ : H) hφ (x : H)

theorem orthogonalCompression_projected (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (x : A.domain) :
    orthogonalCompression A (φ : H) (compressionDomainProjection A φ hφ x) =
      complementProjection (φ : H)
        (A x - inner ℂ (φ : H) (x : H) • A φ) := by
  rw [orthogonalCompression_apply, compressionDomainInclusion_projection,
    A.map_sub, A.map_smul]

theorem orthogonalCompression_dense_domain (A : H →ₗ.[ℂ] H)
    (hA : Dense (A.domain : Set H)) (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) :
    Dense ((orthogonalCompression A (φ : H)).domain : Set (orthogonalComplement (φ : H))) := by
  apply (complementProjection_surjective (φ : H)).denseRange.dense_of_mapsTo
    (complementProjection (φ : H)).continuous hA
  intro x hx
  exact complementProjection_mem_domain A φ hφ hx

/-- Projection can be removed from either side of the compressed inner product. -/
theorem orthogonalCompression_inner (A : H →ₗ.[ℂ] H) (φ : H)
    (y : orthogonalComplement φ) (x : (orthogonalCompression A φ).domain) :
    inner ℂ y (orthogonalCompression A φ x) =
      inner ℂ (y : H) (A (compressionDomainInclusion A φ x)) := by
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left _ _

theorem orthogonalCompression_isFormalAdjoint (A : H →ₗ.[ℂ] H)
    (hA : A.IsFormalAdjoint A) (φ : H) :
    (orthogonalCompression A φ).IsFormalAdjoint (orthogonalCompression A φ) := by
  intro x y
  change inner ℂ (complementProjection φ (A (compressionDomainInclusion A φ x)))
      (y : orthogonalComplement φ) =
    inner ℂ (x : orthogonalComplement φ)
      (complementProjection φ (A (compressionDomainInclusion A φ y)))
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_right,
    Submodule.inner_orthogonalProjection_eq_of_mem_left]
  exact hA (compressionDomainInclusion A φ x) (compressionDomainInclusion A φ y)

variable [CompleteSpace H]

/-- Membership in the compressed adjoint domain forces membership in the
original adjoint domain. The missing one-dimensional term is bounded. -/
theorem orthogonalCompression_adjoint_domain_subset (A : H →ₗ.[ℂ] H)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1)
    {y : orthogonalComplement (φ : H)}
    (hy : y ∈ (orthogonalCompression A (φ : H)).adjoint.domain) :
    (y : H) ∈ A.adjoint.domain := by
  let B := orthogonalCompression A (φ : H)
  have hyC : Continuous (fun x : B.domain => inner ℂ y (B x)) :=
    (B.mem_adjoint_domain_iff y).mp hy
  have hfirst : Continuous (fun x : A.domain =>
      inner ℂ y (B (compressionDomainProjection A φ hφ x))) :=
    hyC.comp (compressionDomainProjection A φ hφ).continuous
  have hsecond : Continuous (fun x : A.domain =>
      inner ℂ (φ : H) (x : H) * inner ℂ (y : H) (A φ)) :=
    (((innerSL ℂ (φ : H)).comp A.domain.subtypeL).continuous).mul continuous_const
  rw [A.mem_adjoint_domain_iff]
  change Continuous (fun x : A.domain => inner ℂ (y : H) (A x))
  convert hfirst.add hsecond using 1
  funext x
  change inner ℂ (y : H) (A x) =
    inner ℂ y (orthogonalCompression A (φ : H) (compressionDomainProjection A φ hφ x)) +
      inner ℂ (φ : H) (x : H) * inner ℂ (y : H) (A φ)
  rw [orthogonalCompression_projected,
    Submodule.inner_orthogonalProjection_eq_of_mem_left, inner_sub_right, inner_smul_right]
  ring

/-- A self-adjoint operator compressed off any unit domain vector is self-adjoint. -/
theorem isSelfAdjoint_orthogonalCompression (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) :
    IsSelfAdjoint (orthogonalCompression A (φ : H)) := by
  have hstar : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hsym : A.IsFormalAdjoint A := by
    simpa only [hstar] using LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  have hBdense := orthogonalCompression_dense_domain A hA.dense_domain φ hφ
  have hle := (orthogonalCompression_isFormalAdjoint A hsym (φ : H)).le_adjoint hBdense
  have hdom : (orthogonalCompression A (φ : H)).domain =
      (orthogonalCompression A (φ : H)).adjoint.domain := by
    apply le_antisymm hle.1
    intro y hy
    have hyA := orthogonalCompression_adjoint_domain_subset A φ hφ hy
    rw [hstar] at hyA
    exact hyA
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hle hdom).symm

end InfiniteZero
