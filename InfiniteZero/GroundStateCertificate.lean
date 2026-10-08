import InfiniteZero.AtomicGroundTransfer

/-!
# A concrete energy certificate identifies the actual ground state

The certificate records a nonzero domain eigenvector, a global lower form
bound, and a positive gap on its orthogonal complement. These data imply the
variational identity, a one-dimensional actual eigenspace, and the precise gap
predicate used by the project. Neither the identity of the variational bottom
nor the eigenspace dimension nor the existence of a smooth state is a field.
-/

noncomputable section

namespace InfiniteZero

/-- Explicit operator and form data supplied by the Schur construction. -/
structure GroundStateCertificate (A : L2Space →ₗ.[ℂ] L2Space) (E : ℝ) where
  vector : A.domain
  vector_ne_zero : (vector : L2Space) ≠ 0
  eigenvector : A vector = (E : ℂ) • (vector : L2Space)
  lower_bound : ∀ u : A.domain,
    E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re
  gap : ℝ
  gap_pos : 0 < gap
  gap_bound : ∀ u : A.domain, inner ℂ (vector : L2Space) (u : L2Space) = 0 →
    (E + gap) * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re

/-- The real energy of an actual real-eigenvalue eigenvector. -/
theorem re_inner_eq_of_operator_eigenvector (A : L2Space →ₗ.[ℂ] L2Space)
    (E : ℝ) (u : A.domain) (hu : A u = (E : ℂ) • (u : L2Space)) :
    (inner ℂ (u : L2Space) (A u)).re = E * ‖(u : L2Space)‖ ^ 2 := by
  have hself : (inner ℂ (u : L2Space) (u : L2Space)).re = ‖(u : L2Space)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (u : L2Space)
  rw [hu, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hself]
  ring

namespace GroundStateCertificate

variable {A : L2Space →ₗ.[ℂ] L2Space} {E : ℝ} (h : GroundStateCertificate A E)

include h

theorem vector_mem_eigenspace : (h.vector : L2Space) ∈ operatorEigenspace A E := by
  rw [mem_operatorEigenspace]
  exact h.eigenvector ▸ A.mem_graph h.vector

def normalizedVector : A.domain :=
  ((‖(h.vector : L2Space)‖⁻¹ : ℝ) : ℂ) • h.vector

theorem normalizedVector_norm : ‖(h.normalizedVector : L2Space)‖ = 1 := by
  have hn : ‖(h.vector : L2Space)‖ ≠ 0 := norm_ne_zero_iff.mpr h.vector_ne_zero
  simp only [normalizedVector, Submodule.coe_smul, norm_smul, Complex.norm_real,
    norm_inv, norm_norm]
  exact inv_mul_cancel₀ hn

theorem normalizedVector_eigenvector :
    A h.normalizedVector = (E : ℂ) • (h.normalizedVector : L2Space) := by
  rw [normalizedVector, A.map_smul, h.eigenvector]
  exact smul_comm _ _ _

/-- Both nonemptiness and boundedness of the defining infimum are proved. -/
theorem variationalBottom_eq : operatorVariationalBottom A = E := by
  let S : Set ℝ := {r | ∃ u : A.domain, ‖(u : L2Space)‖ = 1 ∧
    (inner ℂ (u : L2Space) (A u)).re = r}
  have hE : E ∈ S := by
    refine ⟨h.normalizedVector, h.normalizedVector_norm, ?_⟩
    rw [re_inner_eq_of_operator_eigenvector A E _ h.normalizedVector_eigenvector,
      h.normalizedVector_norm]
    simp
  have hlower : ∀ r ∈ S, E ≤ r := by
    rintro r ⟨u, hu, rfl⟩
    have hh := h.lower_bound u
    simpa only [hu, one_pow, mul_one] using hh
  change sInf S = E
  exact le_antisymm (csInf_le ⟨E, hlower⟩ hE) (le_csInf ⟨E, hE⟩ hlower)

/-- Removing the projection on the certified vector leaves no other eigenvector. -/
theorem eigenvector_eq_smul (u : A.domain)
    (hu : A u = (E : ℂ) • (u : L2Space)) : ∃ c : ℂ, u = c • h.vector := by
  have hself : inner ℂ (h.vector : L2Space) (h.vector : L2Space) ≠ 0 := by
    intro hz
    exact h.vector_ne_zero ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)
  let c : ℂ := inner ℂ (h.vector : L2Space) (u : L2Space) /
    inner ℂ (h.vector : L2Space) (h.vector : L2Space)
  let v : A.domain := u - c • h.vector
  have hvorth : inner ℂ (h.vector : L2Space) (v : L2Space) = 0 := by
    simp only [v, Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right]
    rw [show c * inner ℂ (h.vector : L2Space) (h.vector : L2Space) =
      inner ℂ (h.vector : L2Space) (u : L2Space) from div_mul_cancel₀ _ hself]
    exact sub_self _
  have hveig : A v = (E : ℂ) • (v : L2Space) := by
    simp only [v, A.map_sub, A.map_smul, hu, h.eigenvector,
      Submodule.coe_sub, Submodule.coe_smul, smul_sub, smul_smul]
    rw [mul_comm c (E : ℂ)]
  have hgap := h.gap_bound v hvorth
  rw [re_inner_eq_of_operator_eigenvector A E v hveig] at hgap
  have hvnorm : ‖(v : L2Space)‖ = 0 := by
    have hs : ‖(v : L2Space)‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ h.gap_pos).mp (by nlinarith [hgap])
    exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
  have hvzero : v = 0 := Subtype.ext (norm_eq_zero.mp hvnorm)
  exact ⟨c, sub_eq_zero.mp hvzero⟩

theorem eigenspace_eq_span :
    operatorEigenspace A E = Submodule.span ℂ {(h.vector : L2Space)} := by
  apply le_antisymm
  · intro u hu
    obtain ⟨x, hx, hxA⟩ := A.mem_graph_iff.mp ((mem_operatorEigenspace A E u).mp hu)
    have hxeig : A x = (E : ℂ) • (x : L2Space) := by simpa only [hx] using hxA
    obtain ⟨c, hc⟩ := h.eigenvector_eq_smul x hxeig
    apply Submodule.mem_span_singleton.mpr
    exact ⟨c, (hx.symm.trans (congrArg Subtype.val hc)).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact h.vector_mem_eigenspace

theorem eigenspace_finrank : Module.finrank ℂ (operatorEigenspace A E) = 1 := by
  rw [h.eigenspace_eq_span]
  exact finrank_span_singleton h.vector_ne_zero

theorem hasGapAboveGround : HasGapAboveGround A E := by
  refine ⟨h.gap, h.gap_pos, ?_⟩
  intro u hu
  exact h.gap_bound u (hu (h.vector : L2Space) h.vector_mem_eigenspace)

end GroundStateCertificate

theorem IsMagneticRealization.atomicGroundEnergy_eq_of_certificate
    {b coupling : ℝ} {V : Potential} (hA : IsMagneticRealization b coupling V)
    {E : ℝ} (h : GroundStateCertificate (magneticOperator b coupling V) E) :
    atomicGroundEnergy b V coupling = E :=
  hA.bottom_eq.symm.trans h.variationalBottom_eq

/-- Transfer to the project's smooth normalized atomic states and exact gap predicate. -/
theorem IsMagneticRealization.atomicGround_properties_of_certificate
    {b coupling : ℝ} {V : Potential} (hA : IsMagneticRealization b coupling V)
    {E : ℝ} (h : GroundStateCertificate (magneticOperator b coupling V) E) :
    (∃ φ, IsAtomicGroundState b V coupling φ) ∧
      AtomicGroundSimple b V coupling ∧
      HasGapAboveGround (magneticOperator b coupling V) (atomicGroundEnergy b V coupling) := by
  have hE := hA.atomicGroundEnergy_eq_of_certificate h
  have hv : (h.vector : L2Space) ∈ operatorEigenspace (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling) := by
    rw [hE]
    exact h.vector_mem_eigenspace
  have hdim : Module.finrank ℂ (operatorEigenspace (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling)) = 1 := by
    rw [hE]
    exact h.eigenspace_finrank
  refine ⟨hA.exists_atomicGroundState_of_eigenvector hv h.vector_ne_zero,
    hA.atomicGroundSimple_of_finrank_one hdim, ?_⟩
  rw [hE]
  exact h.hasGapAboveGround

end InfiniteZero
