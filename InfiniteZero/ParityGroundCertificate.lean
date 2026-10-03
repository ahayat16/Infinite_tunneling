import InfiniteZero.ParityEnergyIdentification

/-!
# Certificates for actual ground states in a parity sector

The vector and its eigen-equation belong to the original magnetic operator
domain. A sector lower bound and a positive gap imply the exact parity
energy, a one-dimensional sector eigenspace, and a smooth normalized
physical eigenfunction. These consequences are proved, not certificate fields.
-/

noncomputable section
namespace InfiniteZero

structure ParityGroundCertificate (A : L2Space →ₗ.[ℂ] L2Space) (even : Bool) (E : ℝ) where
  vector : A.domain
  vector_ne_zero : (vector : L2Space) ≠ 0
  parity : HasL2Parity even (vector : L2Space)
  eigenvector : A vector = (E : ℂ) • (vector : L2Space)
  lower_bound : ∀ u : A.domain, HasL2Parity even (u : L2Space) →
    E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re
  gap : ℝ
  gap_pos : 0 < gap
  gap_bound : ∀ u : A.domain, HasL2Parity even (u : L2Space) →
    inner ℂ (vector : L2Space) (u : L2Space) = 0 →
    (E + gap) * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re

def parityOperatorEigenspace (A : L2Space →ₗ.[ℂ] L2Space) (even : Bool) (E : ℝ) :
    Submodule ℂ L2Space := operatorEigenspace A E ⊓ l2ParitySector even

namespace ParityGroundCertificate

variable {A : L2Space →ₗ.[ℂ] L2Space} {even : Bool} {E : ℝ}
variable (h : ParityGroundCertificate A even E)

def normalizedVector : A.domain := ((‖(h.vector : L2Space)‖⁻¹ : ℝ) : ℂ) • h.vector

theorem normalizedVector_norm : ‖(h.normalizedVector : L2Space)‖ = 1 := by
  have hn := norm_ne_zero_iff.mpr h.vector_ne_zero
  simp only [normalizedVector, Submodule.coe_smul, norm_smul, Complex.norm_real,
    norm_inv, norm_norm]
  exact inv_mul_cancel₀ hn

theorem normalizedVector_parity : HasL2Parity even (h.normalizedVector : L2Space) := by
  apply (mem_l2ParitySector_iff even _).mp
  exact (l2ParitySector even).smul_mem _ ((mem_l2ParitySector_iff even _).mpr h.parity)

theorem normalizedVector_eigenvector :
    A h.normalizedVector = (E : ℂ) • (h.normalizedVector : L2Space) := by
  rw [normalizedVector, A.map_smul, h.eigenvector]
  exact smul_comm _ _ _

theorem vector_mem_parityEigenspace :
    (h.vector : L2Space) ∈ parityOperatorEigenspace A even E := by
  refine ⟨?_, (mem_l2ParitySector_iff even _).mpr h.parity⟩
  change (h.vector : L2Space) ∈ operatorEigenspace A E
  rw [mem_operatorEigenspace]
  exact h.eigenvector ▸ A.mem_graph h.vector

theorem eigenvector_eq_smul (u : A.domain) (hp : HasL2Parity even (u : L2Space))
    (hu : A u = (E : ℂ) • (u : L2Space)) : ∃ c : ℂ, u = c • h.vector := by
  have hself : inner ℂ (h.vector : L2Space) (h.vector : L2Space) ≠ 0 := by
    intro hz
    exact h.vector_ne_zero ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)
  let c := inner ℂ (h.vector : L2Space) (u : L2Space) /
    inner ℂ (h.vector : L2Space) (h.vector : L2Space)
  let v : A.domain := u - c • h.vector
  have hvpar : HasL2Parity even (v : L2Space) := by
    apply (mem_l2ParitySector_iff even _).mp
    exact (l2ParitySector even).sub_mem ((mem_l2ParitySector_iff even _).mpr hp)
      ((l2ParitySector even).smul_mem _ ((mem_l2ParitySector_iff even _).mpr h.parity))
  have hvorth : inner ℂ (h.vector : L2Space) (v : L2Space) = 0 := by
    simp only [v, Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right]
    rw [show c * inner ℂ (h.vector : L2Space) (h.vector : L2Space) =
      inner ℂ (h.vector : L2Space) (u : L2Space) from div_mul_cancel₀ _ hself]
    exact sub_self _
  have hveig : A v = (E : ℂ) • (v : L2Space) := by
    simp only [v, A.map_sub, A.map_smul, hu, h.eigenvector,
      Submodule.coe_sub, Submodule.coe_smul, smul_sub, smul_smul]
    rw [mul_comm c (E : ℂ)]
  have hg := h.gap_bound v hvpar hvorth
  rw [re_inner_eq_of_operator_eigenvector A E v hveig] at hg
  have hnorm : ‖(v : L2Space)‖ ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ h.gap_pos).mp (by nlinarith only [hg])
  have hz : v = 0 := Subtype.ext (norm_eq_zero.mp
    (sq_eq_zero_iff.mp (le_antisymm hnorm (sq_nonneg _))))
  exact ⟨c, sub_eq_zero.mp hz⟩

theorem eigenspace_eq_span :
    parityOperatorEigenspace A even E = Submodule.span ℂ {(h.vector : L2Space)} := by
  apply le_antisymm
  · intro u hu
    obtain ⟨x, hx, hxA⟩ := A.mem_graph_iff.mp ((mem_operatorEigenspace A E u).mp hu.1)
    dsimp only [Prod.fst, Prod.snd] at hx hxA
    have hxp : HasL2Parity even (x : L2Space) := by
      rw [hx]
      exact (mem_l2ParitySector_iff even u).mp hu.2
    obtain ⟨c, hc⟩ := h.eigenvector_eq_smul x hxp (by simpa only [hx] using hxA)
    rw [← hx, hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
  · exact Submodule.span_le.mpr (by
      intro u hu
      simpa only [Set.mem_singleton_iff.mp hu] using h.vector_mem_parityEigenspace)

include h in
theorem eigenspace_finrank : Module.finrank ℂ (parityOperatorEigenspace A even E) = 1 := by
  rw [h.eigenspace_eq_span]
  exact finrank_span_singleton h.vector_ne_zero

theorem parityEnergy_eq {b coupling L : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L))
    (h : ParityGroundCertificate
      (magneticOperator b coupling (doubleWellPotential v L)) even E) :
    parityEnergy b v L coupling even = E :=
  hA.parityEnergy_eq_of_domain_ground hV even h.vector h.parity h.vector_ne_zero
    h.eigenvector h.lower_bound

theorem exists_normalized_eigenfunction {b coupling : ℝ} {V : Potential}
    (hA : IsMagneticRealization b coupling V)
    (h : ParityGroundCertificate (magneticOperator b coupling V) even E) :
    ∃ ψ : Wavefunction, IsEigenfunction b coupling V E ψ ∧ mass ψ = 1 ∧ HasParity even ψ := by
  have hmem : (h.normalizedVector : L2Space) ∈ operatorEigenspace
      (magneticOperator b coupling V) E := by
    rw [mem_operatorEigenspace]
    exact h.normalizedVector_eigenvector ▸
      (magneticOperator b coupling V).mem_graph h.normalizedVector
  obtain ⟨ψ, hψ, hrep⟩ := (hA.eigenfunction_iff E _).mp hmem
  refine ⟨ψ, hψ, ?_, hrep.hasParity_of_continuous hψ.1.continuous h.normalizedVector_parity⟩
  rw [← hrep.norm_sq_eq_mass, h.normalizedVector_norm, one_pow]

end ParityGroundCertificate
end InfiniteZero
