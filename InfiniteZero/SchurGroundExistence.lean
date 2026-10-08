import InfiniteZero.SchurEigenvector
import InfiniteZero.CoerciveResolvent

/-!
# Constructing a low eigenvector from complement coercivity

The sole spectral assumptions concern a self-adjoint operator, a unit
domain vector with low Rayleigh quotient, and coercivity on its orthogonal
complement. The compression, its inverses and the scalar root are constructed
by the preceding modules; existence of a low eigenvector is not an input.
-/

noncomputable section
open Set
open scoped NNReal
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem orthogonalCompression_lower_bound (A : H →ₗ.[ℂ] H) (φ : A.domain)
    {c : ℝ} (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      c * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re)
    (u : (orthogonalCompression A (φ : H)).domain) :
    c * ‖(u : orthogonalComplement (φ : H))‖ ^ 2 ≤
      (inner ℂ (u : orthogonalComplement (φ : H)) (orthogonalCompression A (φ : H) u)).re := by
  rw [orthogonalCompression_inner]
  exact hbound (compressionDomainInclusion A (φ : H) u)
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (u : orthogonalComplement (φ : H)).property)

/-- The full nonlinear Schur equation has a solution below the trial energy
threshold, with a correction in the actual compressed operator domain. -/
theorem exists_schur_root_data (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal A φ ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      (E₀ + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    ∃ E ∈ Icc (schurDiagonal A φ - g⁻¹ * ‖schurCoupling A φ‖ ^ 2 - 1) E₀,
      ∃ ζ : (orthogonalCompression A (φ : H)).domain,
        orthogonalCompression A (φ : H) ζ =
          schurCoupling A φ + (E : ℂ) • (ζ : orthogonalComplement (φ : H)) ∧
        inner ℂ (φ : H) (A φ) - (E : ℂ) -
          inner ℂ (schurCoupling A φ) (ζ : orthogonalComplement (φ : H)) = 0 := by
  let C := orthogonalCompression A (φ : H)
  have hC : IsSelfAdjoint C := isSelfAdjoint_orthogonalCompression A hA φ hφ
  have hCbound := orthogonalCompression_lower_bound A φ hbound
  obtain ⟨R, hR, _⟩ := exists_coerciveSelfAdjoint_resolventFamily C hC hg hCbound
  have hpos : 0 ≤ (inner ℂ (schurCoupling A φ) (R E₀ (schurCoupling A φ))).re := by
    apply (hR E₀ le_rfl).1.nonneg_of_lower_bound
    intro u
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hg.le)
      (sq_nonneg ‖(u : orthogonalComplement (φ : H))‖)).trans (hCbound u)
  obtain ⟨E, hE, hroot⟩ := exists_realSchurFunction_zero hC hdiag (schurCoupling A φ) R
    (C := ⟨g⁻¹, inv_nonneg.mpr hg.le⟩)
    (fun E hE => (hR E hE).1) (fun E hE => (hR E hE).2) hpos
  obtain ⟨ζ, hζ, hAζ⟩ := C.mem_graph_iff.mp ((hR E hE.2).1 (schurCoupling A φ))
  refine ⟨E, hE, ζ, ?_, ?_⟩
  · simpa only [hζ] using hAζ
  · have hRs := (hR E hE.2).1.isSelfAdjoint hC
    have hrinner : (((inner ℂ (schurCoupling A φ) (R E (schurCoupling A φ))).re : ℝ) : ℂ) =
        inner ℂ (schurCoupling A φ) (R E (schurCoupling A φ)) :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hRs).coe_re_inner_self_apply
        (schurCoupling A φ)
    rw [hζ]
    change inner ℂ (φ : H) (A φ) - (E : ℂ) -
      inner ℂ (schurCoupling A φ) (R E (schurCoupling A φ)) = 0
    rw [← selfAdjoint_coe_re_inner_apply hA φ, ← hrinner]
    exact_mod_cast hroot

theorem exists_low_eigenvector_of_complement_coercive
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal A φ ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      (E₀ + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    ∃ E ≤ E₀, ∃ u : H, u ≠ 0 ∧ (u, (E : ℂ) • u) ∈ A.graph := by
  obtain ⟨E, hE, ζ, hζ, hs⟩ := exists_schur_root_data A hA φ hφ hg hdiag hbound
  exact ⟨E, hE.2, (φ : H) - ((ζ : orthogonalComplement (φ : H)) : H),
    schur_eigenvector_ne_zero (φ : H) hφ _, schur_eigenvector_graph A hA φ hφ E ζ hζ hs⟩

end InfiniteZero
