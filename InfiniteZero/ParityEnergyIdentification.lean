import InfiniteZero.MagneticParityNormalization
import InfiniteZero.GroundStateCertificate

/-!
# Identification with the parity energy in the original model

A genuine parity eigenvector attaining a lower bound on its sector has
exactly the test-function infimum `parityEnergy`. Both nonemptiness and
boundedness of that infimum are proved. The reverse inequality uses the
projected graph-core argument, rather than compact support of an eigenvector.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

theorem IsMagneticRealization.parity_test_lower_of_operator
    {b coupling L E : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) (even : Bool)
    (hbound : ∀ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      HasL2Parity even (u : L2Space) → E * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator b coupling (doubleWellPotential v L) u)).re)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) (hp : HasParity even ψ) :
    E * mass ψ ≤ magneticForm b coupling (doubleWellPotential v L) ψ := by
  have hc : (hψ.memLp.toLp ψ,
      (hψ.memLp_magneticHamiltonian b coupling hV).toLp
        (magneticHamiltonian b coupling (doubleWellPotential v L) ψ)) ∈
      magneticClosedGraph b coupling (doubleWellPotential v L) := by
    change _ ∈ (magneticClosedGraph b coupling (doubleWellPotential v L) :
      Set (L2Space × L2Space))
    rw [magneticClosedGraph_eq_closure]
    exact subset_closure (hψ.mem_magneticTestGraph b coupling hV)
  rw [← hA.graph_eq] at hc
  obtain ⟨u, hu, hAu⟩ := (magneticOperator b coupling (doubleWellPotential v L)).mem_graph_iff.mp hc
  have hupar : HasL2Parity even (u : L2Space) := by
    rw [hu]
    exact (represents_toLp hψ.memLp).hasL2Parity hp
  have h := hbound u hupar
  rw [hu, hAu, norm_toLp_sq_eq_mass hψ.memLp,
    re_inner_toLp_magneticHamiltonian_eq_magneticForm b coupling hV hψ
      hψ.memLp (hψ.memLp_magneticHamiltonian b coupling hV)] at h
  exact h

theorem IsMagneticRealization.parityEnergy_eq_of_domain_ground
    {b coupling L E : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) (even : Bool)
    (w : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hw : HasL2Parity even (w : L2Space)) (hw0 : (w : L2Space) ≠ 0)
    (heig : magneticOperator b coupling (doubleWellPotential v L) w =
      (E : ℂ) • (w : L2Space))
    (hbound : ∀ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      HasL2Parity even (u : L2Space) → E * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator b coupling (doubleWellPotential v L) u)).re) :
    parityEnergy b v L coupling even = E := by
  let S : Set ℝ := {r | ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ ∧
    magneticForm b coupling (doubleWellPotential v L) ψ = r}
  have hS : S.Nonempty := by
    obtain ⟨ψ, hψ, hp⟩ :=
      hA.exists_normalized_parity_test_of_domain_vector hV even w hw hw0
    exact ⟨_, ψ, hψ, hp, rfl⟩
  have hlower : ∀ r ∈ S, E ≤ r := by
    rintro r ⟨ψ, hψ, hp, rfl⟩
    have h := hA.parity_test_lower_of_operator hV even hbound hψ.1 hp
    simpa only [hψ.2, mul_one] using h
  have hBdd : BddBelow S := ⟨E, hlower⟩
  have htest : ∀ ψ : Wavefunction, IsNormalizedTest ψ → HasParity even ψ →
      sInf S ≤ magneticForm b coupling (doubleWellPotential v L) ψ :=
    fun ψ hψ hp => csInf_le hBdd ⟨ψ, hψ, hp, rfl⟩
  have h := hA.parity_lower_of_normalized_test hV even htest w hw
  rw [re_inner_eq_of_operator_eigenvector _ E w heig] at h
  have hupper : sInf S ≤ E :=
    (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hw0))).mp h
  exact le_antisymm hupper (le_csInf hS hlower)

end InfiniteZero
