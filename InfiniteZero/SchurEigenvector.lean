import InfiniteZero.OrthogonalCompression
import InfiniteZero.SchurScalarRoot

/-!
# The Schur root produces a genuine eigenvector

All vectors below belong to the actual domains of the unbounded operator
and its orthogonal compression. An inverse graph identity and the scalar
Schur equation yield a nonzero point of the original operator graph.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def schurCoupling (A : H →ₗ.[ℂ] H) (φ : A.domain) : orthogonalComplement (φ : H) :=
  complementProjection (φ : H) (A φ)

def schurDiagonal (A : H →ₗ.[ℂ] H) (φ : A.domain) : ℝ :=
  (inner ℂ (φ : H) (A φ)).re

theorem selfAdjoint_coe_re_inner_apply {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (u : A.domain) :
    ((inner ℂ (u : H) (A u)).re : ℂ) = inner ℂ (u : H) (A u) := by
  have hs := selfAdjoint_inner_of_mem_graph hA (A.mem_graph u) (A.mem_graph u)
  have hc : (starRingEnd ℂ) (inner ℂ (u : H) (A u)) = inner ℂ (u : H) (A u) :=
    (inner_conj_symm (A u) (u : H)).trans hs
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

theorem orthogonalCompression_mixed_inner (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (η : (orthogonalCompression A (φ : H)).domain) :
    inner ℂ (φ : H) (A (compressionDomainInclusion A (φ : H) η)) =
      inner ℂ (schurCoupling A φ) (η : orthogonalComplement (φ : H)) := by
  have hs := selfAdjoint_inner_of_mem_graph hA (A.mem_graph φ)
    (A.mem_graph (compressionDomainInclusion A (φ : H) η))
  have hp : inner ℂ (schurCoupling A φ) (η : orthogonalComplement (φ : H)) =
      inner ℂ (A φ) ((η : orthogonalComplement (φ : H)) : H) :=
    Submodule.inner_orthogonalProjection_eq_of_mem_right _ _
  exact hs.symm.trans hp.symm

theorem schur_eigenvector_graph (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) (E : ℝ)
    (ζ : (orthogonalCompression A (φ : H)).domain)
    (hζ : orthogonalCompression A (φ : H) ζ =
      schurCoupling A φ + (E : ℂ) • (ζ : orthogonalComplement (φ : H)))
    (hscalar : inner ℂ (φ : H) (A φ) - (E : ℂ) -
      inner ℂ (schurCoupling A φ) (ζ : orthogonalComplement (φ : H)) = 0) :
    ((φ : H) - ((ζ : orthogonalComplement (φ : H)) : H),
      (E : ℂ) • ((φ : H) - ((ζ : orthogonalComplement (φ : H)) : H))) ∈ A.graph := by
  let η := compressionDomainInclusion A (φ : H) ζ
  have hdiag : inner ℂ (φ : H) (A φ) = (E : ℂ) +
      inner ℂ (schurCoupling A φ) (ζ : orthogonalComplement (φ : H)) := by
    linear_combination hscalar
  have hbase : A φ = (schurCoupling A φ : H) + inner ℂ (φ : H) (A φ) • (φ : H) := by
    rw [schurCoupling, complementProjection_coe (φ : H) hφ]
    module
  have hc := congrArg (fun v : orthogonalComplement (φ : H) => (v : H)) hζ
  have hcomp : A η - inner ℂ (schurCoupling A φ)
      (ζ : orthogonalComplement (φ : H)) • (φ : H) =
      (schurCoupling A φ : H) + (E : ℂ) • (η : H) := by
    simpa only [orthogonalCompression_apply, complementProjection_coe (φ : H) hφ,
      orthogonalCompression_mixed_inner A hA φ ζ] using hc
  have hη : A η = (schurCoupling A φ : H) + (E : ℂ) • (η : H) +
      inner ℂ (schurCoupling A φ) (ζ : orthogonalComplement (φ : H)) • (φ : H) :=
    eq_add_of_sub_eq hcomp
  apply A.mem_graph_iff.mpr
  refine ⟨φ - η, rfl, ?_⟩
  rw [A.map_sub, hbase, hη, hdiag]
  change _ = (E : ℂ) • ((φ : H) - (η : H))
  module

omit [CompleteSpace H] in
theorem schur_eigenvector_ne_zero (φ : H) (hφ : ‖φ‖ = 1)
    (ζ : orthogonalComplement φ) : φ - (ζ : H) ≠ 0 := by
  have horth : inner ℂ φ (ζ : H) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp ζ.property
  have hself : inner ℂ φ φ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]
    norm_num
  intro hz
  have hi := congrArg (fun x : H => inner ℂ φ x) hz
  simp only [inner_sub_right, hself, horth, sub_zero, inner_zero_right] at hi
  exact one_ne_zero hi

/-- A real Schur root for the actual compressed resolvent yields a nonzero
eigenvector of the original operator, with no prior spectral existence input. -/
theorem schur_root_has_eigenvector (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) (E : ℝ)
    (R : orthogonalComplement (φ : H) →L[ℂ] orthogonalComplement (φ : H))
    (hR : IsOperatorResolvent (orthogonalCompression A (φ : H)) E R)
    (hroot : schurDiagonal A φ - E - (inner ℂ (schurCoupling A φ) (R (schurCoupling A φ))).re = 0) :
    ∃ u : H, u ≠ 0 ∧ (u, (E : ℂ) • u) ∈ A.graph := by
  obtain ⟨ζ, hζ, hAζ⟩ := (orthogonalCompression A (φ : H)).mem_graph_iff.mp
    (hR (schurCoupling A φ))
  have hRs := hR.isSelfAdjoint (isSelfAdjoint_orthogonalCompression A hA φ hφ)
  have hrinner : (((inner ℂ (schurCoupling A φ) (R (schurCoupling A φ))).re : ℝ) : ℂ) =
      inner ℂ (schurCoupling A φ) (R (schurCoupling A φ)) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hRs).coe_re_inner_self_apply
      (schurCoupling A φ)
  refine ⟨(φ : H) - ((ζ : orthogonalComplement (φ : H)) : H),
    schur_eigenvector_ne_zero (φ : H) hφ _, ?_⟩
  apply schur_eigenvector_graph A hA φ hφ E ζ
  · simpa only [hζ] using hAζ
  · rw [hζ]
    change inner ℂ (φ : H) (A φ) - (E : ℂ) -
      inner ℂ (schurCoupling A φ) (R (schurCoupling A φ)) = 0
    rw [← selfAdjoint_coe_re_inner_apply hA φ, ← hrinner]
    exact_mod_cast hroot

end InfiniteZero
