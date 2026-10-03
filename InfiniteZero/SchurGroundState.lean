import InfiniteZero.SchurGroundExistence
import InfiniteZero.OrthogonalSchurGeometry
import InfiniteZero.EigenvectorEnergy

/-!
# The reconstructed eigenvector is the simple isolated ground direction

Subtracting its component leaves the shifted energy unchanged. The remaining
vector lies in the reference orthogonal complement. The exact Schur norm
identity transfers its coercivity to a gap above the reconstructed vector;
positivity on all vectors then proves that this eigenvalue is the bottom.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem schur_groundVector_gap (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1)
    (ζ : compressionDomain A (φ : H)) {E E₀ g : ℝ}
    (hg : 0 ≤ g) (hE : E ≤ E₀)
    (hw : A (φ - compressionDomainInclusion A (φ : H) ζ) =
      (E : ℂ) • ((φ - compressionDomainInclusion A (φ : H) ζ : A.domain) : H))
    (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      (E₀ + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re)
    (u : A.domain)
    (horth : inner ℂ ((φ : H) - ((ζ : orthogonalComplement (φ : H)) : H)) (u : H) = 0) :
    g * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re - E * ‖(u : H)‖ ^ 2 := by
  let a := inner ℂ (φ : H) (u : H)
  let η : compressionDomain A (φ : H) := compressionDomainProjection A φ hφ u
  let ξ : compressionDomain A (φ : H) := η + a • ζ
  let w : A.domain := φ - compressionDomainInclusion A (φ : H) ζ
  have hη : compressionDomainInclusion A (φ : H) η = u - a • φ :=
    compressionDomainInclusion_projection A φ hφ u
  have hξ : compressionDomainInclusion A (φ : H) ξ = u - a • w := by
    change compressionDomainInclusion A (φ : H) (η + a • ζ) = _
    rw [map_add, map_smul, hη]
    dsimp only [w]
    module
  have hdecomp : a • (φ : H) + ((η : orthogonalComplement (φ : H)) : H) = (u : H) := by
    have h := congrArg (fun v : A.domain => (v : H)) hη
    change ((η : orthogonalComplement (φ : H)) : H) = (u : H) - a • (φ : H) at h
    rw [h]
    module
  have hn : ‖(u : H)‖ ^ 2 ≤ ‖(ξ : orthogonalComplement (φ : H))‖ ^ 2 := by
    have h := schur_complement_norm_sq_ge (φ : H) hφ a
      (ζ : orthogonalComplement (φ : H)) (η : orthogonalComplement (φ : H))
      (by rwa [hdecomp])
    rw [hdecomp] at h
    exact h
  have hc := orthogonalCompression_lower_bound A φ hbound ξ
  rw [orthogonalCompression_inner] at hc
  have he := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖(ξ : orthogonalComplement (φ : H))‖)
  have hlower : g * ‖(ξ : orthogonalComplement (φ : H))‖ ^ 2 ≤
      (inner ℂ (((ξ : orthogonalComplement (φ : H)) : H))
        (A (compressionDomainInclusion A (φ : H) ξ))).re -
      E * ‖(ξ : orthogonalComplement (φ : H))‖ ^ 2 := by
    nlinarith only [hc, he]
  have henergy := eigenvector_shiftedEnergy_sub A hA w hw u a
  rw [← hξ] at henergy
  exact (mul_le_mul_of_nonneg_left hn hg).trans (hlower.trans_eq henergy.symm)

/-- Complement coercivity and one low trial vector construct a ground
eigenvector and a quantitative gap, on the actual operator domain. -/
theorem exists_groundVector_of_complement_coercive
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (φ : A.domain) (hφ : ‖(φ : H)‖ = 1) {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal A φ ≤ E₀)
    (hbound : ∀ u : A.domain, inner ℂ (φ : H) (u : H) = 0 →
      (E₀ + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) :
    ∃ E ≤ E₀, ∃ w : A.domain, (w : H) ≠ 0 ∧ A w = (E : ℂ) • (w : H) ∧
      (∀ u : A.domain, E * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) ∧
      (∀ u : A.domain, inner ℂ (w : H) (u : H) = 0 →
        (E + g) * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (A u)).re) := by
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
  refine ⟨E, hE.2, w, hw0, hw, ?_, ?_⟩
  · intro u
    have h := shiftedEnergy_nonneg_of_complement A hA hg.le w hw0 hw hgap u
    linarith
  · intro u hu
    have h := hgap u hu
    nlinarith only [h]

end InfiniteZero
