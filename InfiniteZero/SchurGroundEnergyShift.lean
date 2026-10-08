import InfiniteZero.SchurGroundState
import InfiniteZero.SchurGroundEstimates

/-!
# Ground energy and quantitative shift from the same Schur root

This version works in every complex Hilbert space, including the actual
parity sectors. It retains the quadratic energy estimate for the very
root whose reconstructed vector attains the lower form bound.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_groundVector_with_energy_shift_bounds
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal A φ ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      (E₀ + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    ∃ E ≤ E₀, ∃ w : A.domain, (w : H) ≠ 0 ∧ A w = (E : ℂ) • (w : H) ∧
      (∀ u : A.domain, E * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) ∧
      0 ≤ schurDiagonal A φ - E ∧
      schurDiagonal A φ - E ≤ ‖schurCoupling A φ‖ ^ 2 / g := by
  obtain ⟨E, hE, ζ, hζ, hs⟩ := exists_schur_root_data A hA φ hφ hg hdiag hbound
  let w : A.domain := φ - compressionDomainInclusion A (φ : H) ζ
  have hw0 : (w : H) ≠ 0 := schur_eigenvector_ne_zero (φ : H) hφ _
  have hw : A w = (E : ℂ) • (w : H) := by
    obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp (schur_eigenvector_graph A hA φ hφ E ζ hζ hs)
    have hvw : v = w := Subtype.ext hv
    simpa only [hvw] using hAv
  have hgap (u : A.domain) (hu : inner ℂ (w : H) (u : H) = 0) :
      g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re - E * ‖(u : H)‖ ^ 2 :=
    schur_groundVector_gap A hA φ hφ ζ hg.le hE.2 hw hbound u hu
  refine ⟨E, hE.2, w, hw0, hw, ?_, schur_energy_shift_bounds A φ hg hE.2 hbound ζ hζ hs⟩
  intro u
  have h := shiftedEnergy_nonneg_of_complement A hA hg.le w hw0 hw hgap u
  linarith only [h]

end InfiniteZero
