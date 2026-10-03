import InfiniteZero.MagneticBoundedPerturbation
import InfiniteZero.MagneticCovariance
import InfiniteZero.WavefunctionL2Bridge

/-!
# Translated atomic states in the actual double-well operator domain

The closed-graph shear for a bounded potential transports actual atomic
eigenvectors into the double-well domain. The resulting operator residual
is exactly multiplication by the opposite potential. No double-well
eigenfunction or spectral reduction is assumed.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

theorem IsEigenfunction.exists_boundedPerturbation_operator_vector
    {b coupling E : ℝ} {V W : Potential} {ψ : Wavefunction}
    (hψ : IsEigenfunction b coupling V E ψ)
    (hA : IsMagneticRealization b coupling V)
    (hAW : IsMagneticRealization b coupling (V + W))
    (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    ∃ u : (magneticOperator b coupling (V + W)).domain,
      Represents (u : L2Space) ψ ∧
      magneticOperator b coupling (V + W) u =
        (E : ℂ) • (u : L2Space) +
          (coupling ^ 2 : ℂ) • boundedPotentialMul W hW hbound (u : L2Space) := by
  let z : L2Space := hψ.2.1.toLp ψ
  have hz : Represents z ψ := represents_toLp hψ.2.1
  have heig : z ∈ operatorEigenspace (magneticOperator b coupling V) E :=
    (hA.eigenfunction_iff E z).mpr ⟨ψ, hψ, hz⟩
  have hg : (z, (E : ℂ) • z +
      (coupling ^ 2 : ℂ) • boundedPotentialMul W hW hbound z) ∈
      (magneticOperator b coupling (V + W)).graph := by
    rw [hAW.graph_eq]
    apply (magneticGraphShear_mem_closedGraph_iff b coupling V W hW hbound
      (z, (E : ℂ) • z)).mpr
    rwa [← hA.graph_eq]
  obtain ⟨u, hu, hAu⟩ := (LinearPMap.mem_graph_iff _).mp hg
  exact ⟨u, by simpa only [hu] using hz, by simpa only [hu] using hAu⟩

theorem IsAtomicGroundState.exists_leftState_double_operator_vector
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L)) :
    let W : Potential := fun x => v (-x + displacement L)
    let hW : Continuous W := hv.comp (continuous_neg.add continuous_const)
    let B := boundedPotentialMul W hW (fun x => hbound (-x + displacement L))
    ∃ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      Represents (u : L2Space) (leftState b L coupling φ) ∧ ‖(u : L2Space)‖ = 1 ∧
      magneticOperator b coupling (doubleWellPotential v L) u =
        (atomicGroundEnergy b v coupling : ℂ) • (u : L2Space) +
          (coupling ^ 2 : ℂ) • B (u : L2Space) := by
  dsimp only
  obtain ⟨hleft, hmass⟩ := hφ.leftState_eigenfunction L
  obtain ⟨u, hu, hAu⟩ := hleft.exists_boundedPerturbation_operator_vector
    (W := fun x => v (-x + displacement L)) hAleft hAdouble
    (hv.comp (continuous_neg.add continuous_const)) (fun x => hbound (-x + displacement L))
  refine ⟨u, hu, ?_, hAu⟩
  have hs := hu.norm_sq_eq_mass.trans hmass
  nlinarith [norm_nonneg (u : L2Space)]

theorem IsAtomicGroundState.exists_rightState_double_operator_vector
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L)) :
    let W : Potential := fun x => v (x + displacement L)
    let hW : Continuous W := hv.comp (continuous_id.add continuous_const)
    let B := boundedPotentialMul W hW (fun x => hbound (x + displacement L))
    ∃ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      Represents (u : L2Space) (rightState b L coupling φ) ∧ ‖(u : L2Space)‖ = 1 ∧
      magneticOperator b coupling (doubleWellPotential v L) u =
        (atomicGroundEnergy b v coupling : ℂ) • (u : L2Space) +
          (coupling ^ 2 : ℂ) • B (u : L2Space) := by
  dsimp only
  have hpot : (fun x => v (displacement L - x)) + (fun x => v (x + displacement L)) =
      doubleWellPotential v L := by
    funext x
    simp only [Pi.add_apply, doubleWellPotential, sub_eq_add_neg, add_comm]
  obtain ⟨hright, hmass⟩ := hφ.rightState_eigenfunction L
  have hAadd : IsMagneticRealization b coupling
      ((fun x => v (displacement L - x)) + (fun x => v (x + displacement L))) := by
    rw [hpot]
    exact hAdouble
  obtain ⟨u, hu, hAu⟩ := hright.exists_boundedPerturbation_operator_vector
    (W := fun x => v (x + displacement L)) hAright hAadd
    (hv.comp (continuous_id.add continuous_const)) (fun x => hbound (x + displacement L))
  have hn : ‖(u : L2Space)‖ = 1 := by
    have hs := hu.norm_sq_eq_mass.trans hmass
    nlinarith [norm_nonneg (u : L2Space)]
  revert u hu hn hAu
  rw [hpot]
  exact fun u hu hAu hn => ⟨u, hu, hn, hAu⟩

end InfiniteZero
