import InfiniteZero.ParityOperatorDecomposition
import InfiniteZero.SecondEnergyComplementLower

/-!
# The first two global minmax values of a genuine parity doublet

The ground energy is the minimum of the two attained parity bottoms.
If each opposite bottom lies below the other sector's complement floor,
the second test minmax is their maximum. Both assertions use the original
operator and test-function definitions, including at an exact crossing.
-/

noncomputable section
namespace InfiniteZero

theorem operatorVariationalBottom_eq_of_unit_ground_vector
    (A : L2Space →ₗ.[ℂ] L2Space) {E : ℝ} (w : A.domain)
    (hw : ‖(w : L2Space)‖ = 1) (hEig : A w = (E : ℂ) • (w : L2Space))
    (hlower : ∀ u : A.domain, E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re) :
    operatorVariationalBottom A = E := by
  let S : Set ℝ := {r | ∃ u : A.domain, ‖(u : L2Space)‖ = 1 ∧
    (inner ℂ (u : L2Space) (A u)).re = r}
  have hE : E ∈ S := by
    refine ⟨w, hw, ?_⟩
    rw [re_inner_eq_of_operator_eigenvector A E w hEig, hw, one_pow, mul_one]
  have hbound : ∀ r ∈ S, E ≤ r := by
    rintro r ⟨u, hu, rfl⟩
    simpa only [hu, one_pow, mul_one] using hlower u
  exact le_antisymm (csInf_le ⟨E, hbound⟩ hE) (le_csInf ⟨E, hE⟩ hbound)

theorem IsMagneticRealization.groundEnergy_eq_min_of_parityGroundCertificates
    {b coupling L E F : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (c : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L)) true E)
    (d : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L)) false F) :
    groundEnergy b v L coupling = min E F := by
  let A := magneticOperator b coupling (doubleWellPotential v L)
  have hP := hA.parityStarProjection_double_graph
  have hlo := c.global_lower_bound_min hP d
  change variationalBottom b coupling (doubleWellPotential v L) = _
  rw [← hA.bottom_eq]
  rcases le_total E F with hEF | hFE
  · rw [min_eq_left hEF] at hlo ⊢
    exact operatorVariationalBottom_eq_of_unit_ground_vector A c.normalizedVector
      c.normalizedVector_norm c.normalizedVector_eigenvector hlo
  · rw [min_eq_right hFE] at hlo ⊢
    exact operatorVariationalBottom_eq_of_unit_ground_vector A d.normalizedVector
      d.normalizedVector_norm d.normalizedVector_eigenvector hlo

theorem IsMagneticRealization.secondEnergy_eq_max_of_parityGroundCertificates
    {b coupling L E F : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) {B : ℝ}
    (hB : ∀ x, |doubleWellPotential v L x| ≤ B)
    (c : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L)) true E)
    (d : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L)) false F)
    (hfloorE : F ≤ E + c.gap) (hfloorF : E ≤ F + d.gap) :
    secondEnergy b v L coupling = max E F := by
  have hneE := hA.exists_normalized_parity_test_of_domain_vector
    hV true c.vector c.parity c.vector_ne_zero
  have hneF := hA.exists_normalized_parity_test_of_domain_vector
    hV false d.vector d.parity d.vector_ne_zero
  have hupper := secondEnergy_le_max_parityEnergy (b := b) (coupling := coupling) hV hB hneE hneF
  rw [evenEnergy, oddEnergy, c.parityEnergy_eq hA hV, d.parityEnergy_eq hA hV] at hupper
  refine le_antisymm hupper ?_
  rcases le_total E F with hEF | hFE
  · exact hA.secondEnergy_lower_of_domain_orthogonal hV hneE hneF (c.vector : L2Space)
      (fun u hu => c.global_complement_lower_bound_max
        hA.parityStarProjection_double_graph d hEF hfloorE u hu)
  · have hlo := hA.secondEnergy_lower_of_domain_orthogonal hV hneE hneF (d.vector : L2Space)
      (fun u hu => d.global_complement_lower_bound_max
        hA.parityStarProjection_double_graph c hFE hfloorF u hu)
    simpa only [max_comm F E] using hlo

end InfiniteZero
