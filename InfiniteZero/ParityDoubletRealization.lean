import InfiniteZero.PhysicalParityModes
import InfiniteZero.ParityGlobalGroundGap

/-!
# The exact two-mode realization from the constructed sector certificates

This joins global minmax values, normalized classical modes and all
pointwise eigenspace decompositions. The hypotheses are the attained
sector certificates; their physical construction is supplied separately.
-/

noncomputable section
namespace InfiniteZero

theorem twoModeRealization_of_parityGroundCertificates
    {b L threshold : ℝ} {v : Potential}
    (hA : ∀ coupling, IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) {B : ℝ}
    (hB : ∀ x, |doubleWellPotential v L x| ≤ B)
    (hcert : ∀ coupling, threshold ≤ coupling →
      ∃ c : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L))
          true (evenEnergy b v L coupling),
      ∃ d : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L))
          false (oddEnergy b v L coupling),
        oddEnergy b v L coupling ≤ evenEnergy b v L coupling + c.gap ∧
        evenEnergy b v L coupling ≤ oddEnergy b v L coupling + d.gap) :
    TwoModeRealization b v L threshold where
  ordered_ground coupling hc := by
    obtain ⟨c, d, _, _⟩ := hcert coupling hc
    exact (hA coupling).groundEnergy_eq_min_of_parityGroundCertificates c d
  ordered_second coupling hc := by
    obtain ⟨c, d, hcFloor, hdFloor⟩ := hcert coupling hc
    exact (hA coupling).secondEnergy_eq_max_of_parityGroundCertificates hV hB c d hcFloor hdFloor
  crossing_modes coupling hc heq := by
    obtain ⟨c, d, _, _⟩ := hcert coupling hc
    have hg : groundEnergy b v L coupling = evenEnergy b v L coupling :=
      ((hA coupling).groundEnergy_eq_min_of_parityGroundCertificates c d).trans (min_eq_left heq.le)
    rw [← heq] at d
    obtain ⟨φ, ψ, hmφ, hmψ, hpφ, hpψ, _, _, hmodes⟩ :=
      c.exists_normalized_physical_two_modes (hA coupling).parityStarProjection_double_graph d (hA coupling)
    refine ⟨φ, ψ, hmφ, hmψ, hpφ, hpψ, ?_⟩
    intro χ
    change IsEigenfunction b coupling (doubleWellPotential v L) (groundEnergy b v L coupling) χ ↔ _
    rw [hg]
    exact hmodes χ
  even_mode coupling hc hlt := by
    obtain ⟨c, d, _, _⟩ := hcert coupling hc
    have hg : groundEnergy b v L coupling = evenEnergy b v L coupling :=
      ((hA coupling).groundEnergy_eq_min_of_parityGroundCertificates c d).trans (min_eq_left hlt.le)
    obtain ⟨φ, hmφ, hpφ, _, hmode⟩ :=
      c.exists_normalized_physical_one_mode (hA coupling).parityStarProjection_double_graph d hlt (hA coupling)
    refine ⟨φ, hmφ, hpφ, ?_⟩
    intro χ
    change IsEigenfunction b coupling (doubleWellPotential v L) (groundEnergy b v L coupling) χ ↔ _
    rw [hg]
    exact hmode χ
  odd_mode coupling hc hlt := by
    obtain ⟨c, d, _, _⟩ := hcert coupling hc
    have hg : groundEnergy b v L coupling = oddEnergy b v L coupling :=
      ((hA coupling).groundEnergy_eq_min_of_parityGroundCertificates c d).trans (min_eq_right hlt.le)
    obtain ⟨φ, hmφ, hpφ, _, hmode⟩ :=
      d.exists_normalized_physical_one_mode (hA coupling).parityStarProjection_double_graph c hlt (hA coupling)
    refine ⟨φ, hmφ, hpφ, ?_⟩
    intro χ
    change IsEigenfunction b coupling (doubleWellPotential v L) (groundEnergy b v L coupling) χ ↔ _
    rw [hg]
    exact hmode χ

end InfiniteZero
