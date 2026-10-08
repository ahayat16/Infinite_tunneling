import InfiniteZero.ReducingSubspaceRestriction
import InfiniteZero.DoubleWellParityGraph

/-!
# The actual self-adjoint double-well operators on parity sectors

The domain consists exactly of vectors in the full operator domain which
belong to the closed even or odd sector. The operator value is the full
operator value in that sector, with no compression error. Self-adjointness
follows from invariance of the actual closed graph under the parity projection.
-/

noncomputable section

namespace InfiniteZero

variable {b coupling L : ℝ} {v : Potential}

/-- The genuine restriction of the double-well operator to one parity sector. -/
def doubleWellParityOperator
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool) :
    l2ParitySector even →ₗ.[ℂ] l2ParitySector even :=
  reducingRestriction (magneticOperator b coupling (doubleWellPotential v L))
    (l2ParitySector even) (hA.parityStarProjection_double_graph even)

/-- Inclusion of the actual sector domain into the full operator domain. -/
def doubleWellParityDomainInclusion
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool) :
    (doubleWellParityOperator hA even).domain →ₗ[ℂ]
      (magneticOperator b coupling (doubleWellPotential v L)).domain :=
  reducingDomainInclusion (magneticOperator b coupling (doubleWellPotential v L))
    (l2ParitySector even)

@[simp] theorem doubleWellParityOperator_mem_domain_iff
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool)
    (u : l2ParitySector even) :
    u ∈ (doubleWellParityOperator hA even).domain ↔
      (u : L2Space) ∈ (magneticOperator b coupling (doubleWellPotential v L)).domain :=
  Iff.rfl

@[simp] theorem doubleWellParityDomainInclusion_coe
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool)
    (u : (doubleWellParityOperator hA even).domain) :
    (doubleWellParityDomainInclusion hA even u : L2Space) =
      ((u : l2ParitySector even) : L2Space) := rfl

@[simp] theorem doubleWellParityOperator_apply_coe
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool)
    (u : (doubleWellParityOperator hA even).domain) :
    (doubleWellParityOperator hA even u : L2Space) =
      magneticOperator b coupling (doubleWellPotential v L)
        (doubleWellParityDomainInclusion hA even u) := rfl

theorem doubleWellParityOperator_inner_apply
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool)
    (u : l2ParitySector even) (w : (doubleWellParityOperator hA even).domain) :
    inner ℂ u (doubleWellParityOperator hA even w) =
      inner ℂ (u : L2Space)
        (magneticOperator b coupling (doubleWellPotential v L)
          (doubleWellParityDomainInclusion hA even w)) := rfl

theorem doubleWellParityOperator_isSelfAdjoint
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool) :
    IsSelfAdjoint (doubleWellParityOperator hA even) :=
  isSelfAdjoint_reducingRestriction _ _
    (hA.parityStarProjection_double_graph even) hA.selfAdjoint

theorem doubleWellParityOperator_dense_domain
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool) :
    Dense ((doubleWellParityOperator hA even).domain : Set (l2ParitySector even)) :=
  (doubleWellParityOperator_isSelfAdjoint hA even).dense_domain

theorem doubleWellParityOperator_mem_graph_iff
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L)) (even : Bool)
    (u w : l2ParitySector even) :
    (u, w) ∈ (doubleWellParityOperator hA even).graph ↔
      ((u : L2Space), (w : L2Space)) ∈
        (magneticOperator b coupling (doubleWellPotential v L)).graph := by
  let A := magneticOperator b coupling (doubleWellPotential v L)
  let B := doubleWellParityOperator hA even
  constructor
  · intro h
    obtain ⟨x, hx, hBx⟩ := B.mem_graph_iff.mp h
    exact A.mem_graph_iff.mpr
      ⟨doubleWellParityDomainInclusion hA even x,
        congrArg (fun z : l2ParitySector even => (z : L2Space)) hx,
        congrArg (fun z : l2ParitySector even => (z : L2Space)) hBx⟩
  · intro h
    obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp h
    change (x : L2Space) = (u : L2Space) at hx
    change A x = (w : L2Space) at hAx
    have hu : (u : L2Space) ∈ A.domain := by
      rw [← hx]
      exact x.property
    let y : B.domain := ⟨u, hu⟩
    refine B.mem_graph_iff.mpr ⟨y, rfl, ?_⟩
    apply Subtype.ext
    change A (doubleWellParityDomainInclusion hA even y) = (w : L2Space)
    have hy : doubleWellParityDomainInclusion hA even y = x :=
      Subtype.ext hx.symm
    rw [hy]
    exact hAx

end InfiniteZero
