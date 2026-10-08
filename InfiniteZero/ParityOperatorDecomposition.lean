import InfiniteZero.ParityGroundCertificate
import InfiniteZero.DoubleWellParityGraph

/-!
# Global operator bounds from the two actual parity sectors

The parity projections preserve the genuine operator graph. Their domain
lifts split both norm and quadratic energy exactly. Sector ground-state
certificates consequently give a global lower bound and a lower bound on
the orthogonal complement of the lower mode.
-/

noncomputable section
namespace InfiniteZero

variable (A : L2Space →ₗ.[ℂ] L2Space)
variable (hP : ∀ even : Bool, ∀ q ∈ A.graph,
  ((l2ParitySector even).starProjection q.1,
    (l2ParitySector even).starProjection q.2) ∈ A.graph)

/-- The parity projection lifted to the domain of the actual operator. -/
def parityDomainProjection (even : Bool) (u : A.domain) : A.domain :=
  ⟨l2ParityProjection even (u : L2Space), by
    have hg := hP even ((u : L2Space), A u) (A.mem_graph u)
    rw [← l2ParityProjection_eq_starProjection even] at hg
    obtain ⟨w, hw, _⟩ := A.mem_graph_iff.mp hg
    dsimp only [Prod.fst, Prod.snd] at hw
    rw [← hw]
    exact w.property⟩

@[simp] theorem parityDomainProjection_coe (even : Bool) (u : A.domain) :
    (parityDomainProjection A hP even u : L2Space) =
      l2ParityProjection even (u : L2Space) := rfl

theorem parityDomainProjection_parity (even : Bool) (u : A.domain) :
    HasL2Parity even (parityDomainProjection A hP even u : L2Space) :=
  (mem_l2ParitySector_iff even _).mp (l2ParityProjection_mem even _)

@[simp] theorem parityDomainProjection_apply (even : Bool) (u : A.domain) :
    A (parityDomainProjection A hP even u) = l2ParityProjection even (A u) := by
  have hg := hP even ((u : L2Space), A u) (A.mem_graph u)
  rw [← l2ParityProjection_eq_starProjection even] at hg
  obtain ⟨w, hw, hAw⟩ := A.mem_graph_iff.mp hg
  have hw' : w = parityDomainProjection A hP even u := Subtype.ext hw
  simpa only [hw'] using hAw

theorem parityDomainProjection_add_not (even : Bool) (u : A.domain) :
    parityDomainProjection A hP even u + parityDomainProjection A hP (!even) u = u := by
  apply Subtype.ext
  exact l2ParityProjection_add_not even (u : L2Space)

/-- The global squared norm is exactly the sum of the squared sector norms. -/
theorem norm_sq_eq_parityDomainProjection_add (even : Bool) (u : A.domain) :
    ‖(u : L2Space)‖ ^ 2 =
      ‖(parityDomainProjection A hP even u : L2Space)‖ ^ 2 +
      ‖(parityDomainProjection A hP (!even) u : L2Space)‖ ^ 2 := by
  have ho : inner ℂ (l2ParityProjection even (u : L2Space))
      (l2ParityProjection (!even) (u : L2Space)) = 0 :=
    inner_eq_zero_of_mem_l2ParitySectors (l2ParityProjection_mem even _)
      (l2ParityProjection_mem (!even) _)
  have hn := norm_add_sq (𝕜 := ℂ) (l2ParityProjection even (u : L2Space))
    (l2ParityProjection (!even) (u : L2Space))
  simpa only [l2ParityProjection_add_not, ho, map_zero, mul_zero, add_zero,
    parityDomainProjection_coe] using hn

/-- The actual operator quadratic form is exactly diagonal in parity. -/
theorem inner_operator_eq_parityDomainProjection_add (even : Bool) (u : A.domain) :
    inner ℂ (u : L2Space) (A u) =
      inner ℂ (parityDomainProjection A hP even u : L2Space)
        (A (parityDomainProjection A hP even u)) +
      inner ℂ (parityDomainProjection A hP (!even) u : L2Space)
        (A (parityDomainProjection A hP (!even) u)) := by
  have hcross : inner ℂ (l2ParityProjection even (u : L2Space))
      (l2ParityProjection (!even) (A u)) = 0 :=
    inner_eq_zero_of_mem_l2ParitySectors (l2ParityProjection_mem even _)
      (l2ParityProjection_mem (!even) _)
  have hcross' : inner ℂ (l2ParityProjection (!even) (u : L2Space))
      (l2ParityProjection even (A u)) = 0 := by
    apply inner_eq_zero_of_mem_l2ParitySectors (l2ParityProjection_mem (!even) _)
    simpa only [Bool.not_not] using l2ParityProjection_mem even (A u)
  have he := congrArg₂ (inner ℂ) (l2ParityProjection_add_not even (u : L2Space))
    (l2ParityProjection_add_not even (A u))
  simpa only [inner_add_left, inner_add_right, hcross, hcross', add_zero, zero_add,
    parityDomainProjection_coe, parityDomainProjection_apply] using he.symm

/-- Orthogonality to a vector of one parity is inherited by that projection. -/
theorem inner_parityDomainProjection_eq {even : Bool} {w : L2Space}
    (hw : HasL2Parity even w) (u : A.domain) :
    inner ℂ w (parityDomainProjection A hP even u : L2Space) = inner ℂ w (u : L2Space) := by
  have ho : inner ℂ w (l2ParityProjection (!even) (u : L2Space)) = 0 :=
    inner_eq_zero_of_mem_l2ParitySectors ((mem_l2ParitySector_iff even w).mpr hw)
      (l2ParityProjection_mem (!even) _)
  have he := congrArg (inner ℂ w) (l2ParityProjection_add_not even (u : L2Space))
  simpa only [inner_add_right, ho, add_zero, parityDomainProjection_coe] using he

namespace ParityGroundCertificate

variable {A} {even : Bool} {E F : ℝ}
include hP

/-- Two opposite sector floors imply the minimum floor on the whole domain. -/
theorem global_lower_bound_min
    (c : ParityGroundCertificate A even E) (d : ParityGroundCertificate A (!even) F)
    (u : A.domain) :
    min E F * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re := by
  have hc := c.lower_bound (parityDomainProjection A hP even u)
    (parityDomainProjection_parity A hP even u)
  have hd := d.lower_bound (parityDomainProjection A hP (!even) u)
    (parityDomainProjection_parity A hP (!even) u)
  have hmE := mul_le_mul_of_nonneg_right (min_le_left E F)
    (sq_nonneg ‖(parityDomainProjection A hP even u : L2Space)‖)
  have hmF := mul_le_mul_of_nonneg_right (min_le_right E F)
    (sq_nonneg ‖(parityDomainProjection A hP (!even) u : L2Space)‖)
  rw [norm_sq_eq_parityDomainProjection_add A hP even u,
    inner_operator_eq_parityDomainProjection_add A hP even u, Complex.add_re]
  nlinarith only [hc, hd, hmE, hmF]

/-- If the opposite ground energy lies below this sector's complement floor,
the whole complement of this mode has that opposite ground energy as floor. -/
theorem global_complement_lower_bound
    (c : ParityGroundCertificate A even E) (d : ParityGroundCertificate A (!even) F)
    (hfloor : F ≤ E + c.gap) (u : A.domain)
    (hu : inner ℂ (c.vector : L2Space) (u : L2Space) = 0) :
    F * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re := by
  have huP : inner ℂ (c.vector : L2Space)
      (parityDomainProjection A hP even u : L2Space) = 0 := by
    rw [inner_parityDomainProjection_eq A hP c.parity u, hu]
  have hc := c.gap_bound (parityDomainProjection A hP even u)
    (parityDomainProjection_parity A hP even u) huP
  have hd := d.lower_bound (parityDomainProjection A hP (!even) u)
    (parityDomainProjection_parity A hP (!even) u)
  have hf := mul_le_mul_of_nonneg_right hfloor
    (sq_nonneg ‖(parityDomainProjection A hP even u : L2Space)‖)
  rw [norm_sq_eq_parityDomainProjection_add A hP even u,
    inner_operator_eq_parityDomainProjection_add A hP even u, Complex.add_re]
  nlinarith only [hc, hd, hf]

/-- The preceding bound is the maximum of the two ground energies when the
chosen certificate is the lower mode; equality of the two energies is allowed. -/
theorem global_complement_lower_bound_max
    (c : ParityGroundCertificate A even E) (d : ParityGroundCertificate A (!even) F)
    (hEF : E ≤ F) (hfloor : F ≤ E + c.gap) (u : A.domain)
    (hu : inner ℂ (c.vector : L2Space) (u : L2Space) = 0) :
    max E F * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re := by
  rw [max_eq_right hEF]
  exact c.global_complement_lower_bound hP d hfloor u hu

end ParityGroundCertificate
end InfiniteZero
