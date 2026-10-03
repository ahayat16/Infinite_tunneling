import InfiniteZero.ReducingSubspaceRestriction
import InfiniteZero.ParityGroundCertificate
import InfiniteZero.SchurGroundState
import InfiniteZero.EigenvectorComplementBound

/-!
# Schur construction of a genuine parity ground state

The closed parity sector is a reducing subspace of the original operator.
Applying the already proved Schur construction to its genuine restriction
produces an eigenvector of the original operator, with sector lower bound
and gap. The low trial and complement bound are the only spectral estimates
required by this abstract construction.
-/

noncomputable section
namespace InfiniteZero

theorem exists_parityGroundCertificate_of_complement_coercive
    (A : L2Space →ₗ.[ℂ] L2Space) (hA : IsSelfAdjoint A) (even : Bool)
    (hP : ∀ q ∈ A.graph,
      ((l2ParitySector even).starProjection q.1,
        (l2ParitySector even).starProjection q.2) ∈ A.graph)
    (φ : A.domain) (hφ : ‖(φ : L2Space)‖ = 1)
    (hpar : HasL2Parity even (φ : L2Space)) {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal A φ ≤ E₀)
    (hbound : ∀ u : A.domain, HasL2Parity even (u : L2Space) →
      inner ℂ (φ : L2Space) (u : L2Space) = 0 →
      (E₀ + g) * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re) :
    ∃ E ≤ E₀, ∃ c : ParityGroundCertificate A even E,
      c.gap = E₀ + g - E ∧ g ≤ c.gap := by
  let K := l2ParitySector even
  let B := reducingRestriction A K hP
  have hB : IsSelfAdjoint B := isSelfAdjoint_reducingRestriction A K hP hA
  let φB : B.domain := ⟨⟨(φ : L2Space), (mem_l2ParitySector_iff even _).mpr hpar⟩,
    φ.property⟩
  have hnB : ‖(φB : K)‖ = 1 := hφ
  have hdiagB : schurDiagonal B φB ≤ E₀ := hdiag
  have hboundB : ∀ u : B.domain, inner ℂ (φB : K) (u : K) = 0 →
      (E₀ + g) * ‖(u : K)‖ ^ 2 ≤ (inner ℂ (u : K) (B u)).re := by
    intro u hu
    exact hbound (reducingDomainInclusion A K u)
      ((mem_l2ParitySector_iff even _).mp (u : K).property) hu
  obtain ⟨E, hE, w, hw0, heig, hlower, _hgap⟩ :=
    exists_groundVector_of_complement_coercive B hB φB hnB hg hdiagB hboundB
  have hEC : E < E₀ + g := by linarith only [hE, hg]
  have hgap := eigenvector_complement_lower_of_trial_complement
    B hB (φB : K) hEC w hw0 heig hboundB
  let wA : A.domain := reducingDomainInclusion A K w
  have hwA0 : (wA : L2Space) ≠ 0 := by
    intro hz
    apply hw0
    exact Subtype.ext hz
  have heigA : A wA = (E : ℂ) • (wA : L2Space) :=
    congrArg (fun x : K => (x : L2Space)) heig
  have hlowerA : ∀ u : A.domain, HasL2Parity even (u : L2Space) →
      E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re := by
    intro u hu
    exact hlower ⟨⟨(u : L2Space), (mem_l2ParitySector_iff even _).mpr hu⟩, u.property⟩
  have hgapA : ∀ u : A.domain, HasL2Parity even (u : L2Space) →
      inner ℂ (wA : L2Space) (u : L2Space) = 0 →
      (E + (E₀ + g - E)) * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space) (A u)).re := by
    intro u hu horth
    have h := hgap ⟨⟨(u : L2Space), (mem_l2ParitySector_iff even _).mpr hu⟩, u.property⟩ horth
    change (E₀ + g) * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (A u)).re at h
    convert h using 1
    ring
  exact ⟨E, hE, ⟨wA, hwA0, (mem_l2ParitySector_iff even _).mp (w : K).property,
    heigA, hlowerA, E₀ + g - E, sub_pos.mpr hEC, hgapA⟩,
      rfl, by dsimp; linarith only [hE]⟩

end InfiniteZero
