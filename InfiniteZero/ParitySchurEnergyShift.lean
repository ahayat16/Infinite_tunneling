import InfiniteZero.SchurGroundEnergyShift
import InfiniteZero.DoubleWellParityOperator
import InfiniteZero.ParityEnergyIdentification
import InfiniteZero.SchurResidualBounds

/-!
# The physical parity energy differs quadratically from its trial energy

The Schur root is constructed on the true self-adjoint parity restriction
and identified with the original test infimum. Projection contractivity
then bounds its energy correction by the squared full residual divided
by the complement gap. No relative tunneling estimate is assumed here.
-/

noncomputable section
namespace InfiniteZero

theorem IsMagneticRealization.parityEnergy_shift_bounds_of_complement_coercive
    {b coupling L : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) (even : Bool)
    (φ : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hφ : ‖(φ : L2Space)‖ = 1) (hpar : HasL2Parity even (φ : L2Space))
    {E₀ g : ℝ} (hg : 0 < g)
    (hdiag : schurDiagonal (magneticOperator b coupling (doubleWellPotential v L)) φ ≤ E₀)
    (hbound : ∀ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      HasL2Parity even (u : L2Space) → inner ℂ (φ : L2Space) (u : L2Space) = 0 →
      (E₀ + g) * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space) (magneticOperator b coupling (doubleWellPotential v L) u)).re)
    (Eref : ℝ) :
    0 ≤ schurDiagonal (magneticOperator b coupling (doubleWellPotential v L)) φ -
        parityEnergy b v L coupling even ∧
      schurDiagonal (magneticOperator b coupling (doubleWellPotential v L)) φ -
        parityEnergy b v L coupling even ≤
        ‖magneticOperator b coupling (doubleWellPotential v L) φ -
          (Eref : ℂ) • (φ : L2Space)‖ ^ 2 / g := by
  let A := magneticOperator b coupling (doubleWellPotential v L)
  let K := l2ParitySector even
  let B := doubleWellParityOperator hA even
  let φB : B.domain := ⟨⟨(φ : L2Space), (mem_l2ParitySector_iff even _).mpr hpar⟩,
    φ.property⟩
  have hnB : ‖(φB : K)‖ = 1 := hφ
  have hdiagB : schurDiagonal B φB ≤ E₀ := hdiag
  have hboundB : ∀ u : B.domain, inner ℂ (φB : K) (u : K) = 0 →
      (E₀ + g) * ‖(u : K)‖ ^ 2 ≤ (inner ℂ (u : K) (B u)).re := by
    intro u hu
    exact hbound (doubleWellParityDomainInclusion hA even u)
      ((mem_l2ParitySector_iff even _).mp (u : K).property) hu
  obtain ⟨E, _, w, hw0, heig, hlower, hshift0, hshift⟩ :=
    exists_groundVector_with_energy_shift_bounds B (doubleWellParityOperator_isSelfAdjoint hA even)
      φB hnB hg hdiagB hboundB
  let wA : A.domain := doubleWellParityDomainInclusion hA even w
  have hwA0 : (wA : L2Space) ≠ 0 := fun hz => hw0 (Subtype.ext hz)
  have heigA : A wA = (E : ℂ) • (wA : L2Space) :=
    congrArg (fun x : K => (x : L2Space)) heig
  have hlowerA : ∀ u : A.domain, HasL2Parity even (u : L2Space) →
      E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re := by
    intro u hu
    exact hlower ⟨⟨(u : L2Space), (mem_l2ParitySector_iff even _).mpr hu⟩, u.property⟩
  have hE := hA.parityEnergy_eq_of_domain_ground hV even wA
    ((mem_l2ParitySector_iff even _).mp (w : K).property) hwA0 heigA hlowerA
  rw [hE]
  refine ⟨hshift0, hshift.trans ?_⟩
  have hc := schurCoupling_norm_le_residual B φB hnB Eref
    (B φB - (Eref : ℂ) • (φB : K)) (by module)
  have hsq : ‖schurCoupling B φB‖ ^ 2 ≤
      ‖B φB - (Eref : ℂ) • (φB : K)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hc 2
  exact div_le_div_of_nonneg_right hsq hg.le

end InfiniteZero
