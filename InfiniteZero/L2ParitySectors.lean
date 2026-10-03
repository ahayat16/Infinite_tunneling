import InfiniteZero.L2Inversion
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Closed parity sectors and their explicit orthogonal projections

The sectors are kernels of the continuous maps `J - I` and `J + I`, where
`J` is actual spatial inversion on physical L². The maps `(I + J)/2` and
`(I - J)/2` are identified with mathlib's orthogonal projections.
-/

noncomputable section

namespace InfiniteZero

def l2ParitySector (even : Bool) : Submodule ℂ L2Space :=
  (l2Inversion.toLinearIsometry.toContinuousLinearMap -
    if even then ContinuousLinearMap.id ℂ L2Space
    else -ContinuousLinearMap.id ℂ L2Space).ker

theorem mem_l2ParitySector_iff_inversion (even : Bool) (u : L2Space) :
    u ∈ l2ParitySector even ↔ l2Inversion u = if even then u else -u := by
  cases even
  · change l2Inversion u - -u = 0 ↔ l2Inversion u = -u
    exact sub_eq_zero
  · change l2Inversion u - u = 0 ↔ l2Inversion u = u
    exact sub_eq_zero

theorem mem_l2ParitySector_iff (even : Bool) (u : L2Space) :
    u ∈ l2ParitySector even ↔ HasL2Parity even u :=
  (mem_l2ParitySector_iff_inversion even u).trans (l2Inversion_eq_iff_hasL2Parity even u)

theorem isClosed_l2ParitySector (even : Bool) :
    IsClosed (l2ParitySector even : Set L2Space) :=
  ContinuousLinearMap.isClosed_ker _

instance (even : Bool) : CompleteSpace (l2ParitySector even) :=
  (isClosed_l2ParitySector even).completeSpace_coe

def l2ParityProjection (even : Bool) : L2Space →L[ℂ] L2Space :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ L2Space +
    if even then l2Inversion.toLinearIsometry.toContinuousLinearMap
    else -l2Inversion.toLinearIsometry.toContinuousLinearMap)

theorem l2ParityProjection_apply (even : Bool) (u : L2Space) :
    l2ParityProjection even u =
      (1 / 2 : ℂ) • (u + if even then l2Inversion u else -l2Inversion u) := by
  cases even <;> rfl

theorem l2ParityProjection_mem (even : Bool) (u : L2Space) :
    l2ParityProjection even u ∈ l2ParitySector even := by
  rw [mem_l2ParitySector_iff_inversion, l2ParityProjection_apply]
  cases even <;>
    simp only [Bool.false_eq_true, ↓reduceIte, map_smul, map_add, map_neg,
      l2Inversion_apply_twice] <;> module

theorem l2ParityProjection_eq_self {even : Bool} {u : L2Space}
    (hu : u ∈ l2ParitySector even) : l2ParityProjection even u = u := by
  have hi := (mem_l2ParitySector_iff_inversion even u).mp hu
  rw [l2ParityProjection_apply, hi]
  cases even <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_neg] <;> module

@[simp] theorem l2ParityProjection_apply_twice (even : Bool) (u : L2Space) :
    l2ParityProjection even (l2ParityProjection even u) = l2ParityProjection even u :=
  l2ParityProjection_eq_self (l2ParityProjection_mem even u)

theorem inner_eq_zero_of_mem_l2ParitySectors {even : Bool} {u v : L2Space}
    (hu : u ∈ l2ParitySector even) (hv : v ∈ l2ParitySector (!even)) :
    inner ℂ u v = 0 := by
  have huJ := (mem_l2ParitySector_iff_inversion even u).mp hu
  have hvJ := (mem_l2ParitySector_iff_inversion (!even) v).mp hv
  have hi := inner_l2Inversion u v
  rw [huJ, hvJ] at hi
  cases even <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, inner_neg_left, inner_neg_right] at hi <;>
    linear_combination -(1 / 2 : ℂ) * hi

theorem l2ParityProjection_add_not (even : Bool) (u : L2Space) :
    l2ParityProjection even u + l2ParityProjection (!even) u = u := by
  rw [l2ParityProjection_apply, l2ParityProjection_apply]
  cases even <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] <;> module

theorem l2ParityProjection_eq_starProjection (even : Bool) :
    l2ParityProjection even = (l2ParitySector even).starProjection := by
  apply ContinuousLinearMap.ext
  intro u
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (l2ParityProjection_mem even u)
  intro v hv
  have hsub : u - l2ParityProjection even u = l2ParityProjection (!even) u := by
    have hadd := l2ParityProjection_add_not even u
    rw [sub_eq_iff_eq_add]
    exact hadd.symm.trans (add_comm _ _)
  rw [hsub]
  apply inner_eq_zero_of_mem_l2ParitySectors (l2ParityProjection_mem (!even) u)
  simpa only [Bool.not_not] using hv

def l2ParityProjectionToSector (even : Bool) : L2Space →L[ℂ] l2ParitySector even :=
  (l2ParityProjection even).codRestrict (l2ParitySector even) (l2ParityProjection_mem even)

@[simp] theorem l2ParityProjectionToSector_coe (even : Bool) (u : L2Space) :
    (l2ParityProjectionToSector even u : L2Space) = l2ParityProjection even u := rfl

theorem l2ParityProjectionToSector_surjective (even : Bool) :
    Function.Surjective (l2ParityProjectionToSector even) := by
  intro u
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact l2ParityProjection_eq_self u.property

end InfiniteZero
