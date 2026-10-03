import InfiniteZero.ParityGroundEigenspaces
import InfiniteZero.ParityGlobalMinmax

/-!
# Isolation of the global ground level, including at a crossing

The gap is positive at each coupling. Away from a crossing its lower bound
includes the separation of the two sector bottoms; at a crossing the two
vectors belong to the ground eigenspace and the sector gaps suffice.
No uniform lower bound on the first splitting is asserted.
-/

noncomputable section
namespace InfiniteZero

theorem IsMagneticRealization.ground_gap_of_parityGroundCertificates
    {b coupling L E F : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (c : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L)) true E)
    (d : ParityGroundCertificate (magneticOperator b coupling (doubleWellPotential v L)) false F) :
    HasGapAboveGround (magneticOperator b coupling (doubleWellPotential v L))
      (groundEnergy b v L coupling) := by
  rw [hA.groundEnergy_eq_min_of_parityGroundCertificates c d]
  rcases lt_trichotomy E F with hEF | rfl | hFE
  · rw [min_eq_left hEF.le]
    exact c.global_hasGapAboveGround_of_lt hA.parityStarProjection_double_graph d hEF
  · rw [min_self]
    exact c.global_hasGapAboveGround_at_crossing hA.parityStarProjection_double_graph d
  · rw [min_eq_right hFE.le]
    exact d.global_hasGapAboveGround_of_lt hA.parityStarProjection_double_graph c hFE

end InfiniteZero
