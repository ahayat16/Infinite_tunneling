import InfiniteZero.SchurGroundState
import InfiniteZero.GroundStateCertificate

/-! The general Schur construction supplies every field of the concrete
ground-state certificate. No ground eigenvector, simplicity or gap is assumed. -/

noncomputable section
namespace InfiniteZero

theorem exists_groundStateCertificate_of_complement_coercive
    (A : L2Space →ₗ.[ℂ] L2Space) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : L2Space)‖ = 1) {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal A φ ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : L2Space) (u : L2Space) = 0 →
      (E₀ + g) * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re) :
    ∃ E ≤ E₀, ∃ c : GroundStateCertificate A E, c.gap = g := by
  obtain ⟨E, hE, w, hw0, hw, hlower, hgap⟩ :=
    exists_groundVector_of_complement_coercive A hA φ hφ hg hdiag hbound
  exact ⟨E, hE, ⟨w, hw0, hw, hlower, g, hg, hgap⟩, rfl⟩

end InfiniteZero
