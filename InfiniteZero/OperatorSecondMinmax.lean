import InfiniteZero.GroundStateRankOne
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The second operator min-max and the ground-state gap

The second min-max is defined using two-dimensional subspaces of the actual
operator domain. Its lower bound controls every vector orthogonal to a ground
eigenvector: the ground vector and such a vector span an admissible test space.
This finite-dimensional argument supplies the complement inequality used in
`GroundStateCertificate` without a spectral-theorem admission.
-/

noncomputable section
namespace InfiniteZero

/-- Upper bounds for the Rayleigh form on a two-dimensional operator-domain
subspace. The normalization uses the ambient `L²` norm. -/
def operatorSecondUpperBounds (A : L2Space →ₗ.[ℂ] L2Space) : Set ℝ :=
  {E | ∃ F : Submodule ℂ A.domain,
    Module.finrank ℂ F = 2 ∧
    ∀ u ∈ F, ‖(u : L2Space)‖ = 1 → (inner ℂ (u : L2Space) (A u)).re ≤ E}

/-- The second variational level on the actual operator domain. -/
def operatorSecondMinmax (A : L2Space →ₗ.[ℂ] L2Space) : ℝ :=
  sInf (operatorSecondUpperBounds A)

/-- Homogeneity of the real quadratic energy of an operator. -/
theorem operatorEnergy_smul (A : L2Space →ₗ.[ℂ] L2Space)
    (a : ℂ) (u : A.domain) :
    (inner ℂ ((a • u : A.domain) : L2Space) (A (a • u))).re =
      ‖a‖ ^ 2 * (inner ℂ (u : L2Space) (A u)).re := by
  rw [A.map_smul]
  change (inner ℂ (a • (u : L2Space)) (a • A u)).re = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A positive-dimensional domain subspace contains a unit vector. -/
theorem exists_operator_unit_in_submodule (A : L2Space →ₗ.[ℂ] L2Space)
    (F : Submodule ℂ A.domain) (hF : 0 < Module.finrank ℂ F) :
    ∃ u ∈ F, ‖(u : L2Space)‖ = 1 := by
  letI : Nontrivial F := Module.nontrivial_of_finrank_pos hF
  obtain ⟨u, hu⟩ := exists_ne (0 : F)
  have hu0 : ((u : A.domain) : L2Space) ≠ 0 := by
    intro h
    exact hu (Subtype.ext (Subtype.ext h))
  let a : ℂ := (‖((u : A.domain) : L2Space)‖⁻¹ : ℝ)
  refine ⟨a • (u : A.domain), F.smul_mem _ u.property, ?_⟩
  change ‖a • ((u : A.domain) : L2Space)‖ = 1
  simp only [a, norm_smul, Complex.norm_real, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)

/-- A global form lower bound also bounds below the set defining the second
min-max. This avoids relying on the default value of an unbounded infimum. -/
theorem operatorSecondUpperBounds_bddBelow {A : L2Space →ₗ.[ℂ] L2Space}
    {E : ℝ} (hE : ∀ u : A.domain,
      E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re) :
    BddBelow (operatorSecondUpperBounds A) := by
  refine ⟨E, ?_⟩
  rintro r ⟨F, hF, hr⟩
  obtain ⟨u, hu, hunit⟩ := exists_operator_unit_in_submodule A F (by omega)
  have h := hE u
  simp only [hunit, one_pow, mul_one] at h
  exact h.trans (hr u hu hunit)

/-- Two nonzero orthogonal domain vectors span a two-dimensional space. -/
theorem operator_finrank_span_orthogonal_pair {A : L2Space →ₗ.[ℂ] L2Space}
    (v w : A.domain) (hv : (v : L2Space) ≠ 0) (hw : (w : L2Space) ≠ 0)
    (horth : inner ℂ (v : L2Space) (w : L2Space) = 0) :
    Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set A.domain)) = 2 := by
  let modes : Fin 2 → A.domain := ![v, w]
  have hLI : LinearIndependent ℂ modes := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      fin_cases i
      · exact fun h => hv (congrArg Subtype.val h)
      · exact fun h => hw (congrArg Subtype.val h)
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact horth
      · exact (inner_eq_zero_symm).mp horth
      · exact (hij rfl).elim
  have hrange : Set.range modes = ({v, w} : Set A.domain) := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [modes]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hrange]
  simpa only [Fintype.card_fin] using finrank_span_eq_card hLI

set_option maxHeartbeats 800000 in
/-- The form is diagonal on a ground vector and a unit orthogonal vector.
Their span therefore gives an upper bound on the second min-max. -/
theorem max_operatorEnergy_mem_secondUpperBounds
    {A : L2Space →ₗ.[ℂ] L2Space} (hA : IsSelfAdjoint A)
    {E : ℝ} (v w : A.domain) (hv : ‖(v : L2Space)‖ = 1)
    (hw : ‖(w : L2Space)‖ = 1) (heig : A v = (E : ℂ) • (v : L2Space))
    (horth : inner ℂ (v : L2Space) (w : L2Space) = 0) :
    max E (inner ℂ (w : L2Space) (A w)).re ∈ operatorSecondUpperBounds A := by
  have hv0 : (v : L2Space) ≠ 0 := by intro h; simp [h] at hv
  have hw0 : (w : L2Space) ≠ 0 := by intro h; simp [h] at hw
  refine ⟨Submodule.span ℂ ({v, w} : Set A.domain),
    operator_finrank_span_orthogonal_pair v w hv0 hw0 horth, ?_⟩
  intro u hu hunit
  obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hnorm : ‖((a • v + c • w : A.domain) : L2Space)‖ ^ 2 =
      ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
    change ‖a • (v : L2Space) + c • (w : L2Space)‖ ^ 2 = _
    rw [norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, horth]
    simp [norm_smul, hv, hw]
  have hshift := eigenvector_shiftedEnergy_sub A hA v heig (a • v + c • w) a
  rw [show a • v + c • w - a • v = c • w by module, operatorEnergy_smul] at hshift
  have hcw : ‖((c • w : A.domain) : L2Space)‖ ^ 2 = ‖c‖ ^ 2 := by
    change ‖c • (w : L2Space)‖ ^ 2 = _
    simp [norm_smul, hw]
  rw [hcw, hnorm] at hshift
  have henergy : (inner ℂ ((a • v + c • w : A.domain) : L2Space)
      (A (a • v + c • w))).re =
      ‖a‖ ^ 2 * E + ‖c‖ ^ 2 * (inner ℂ (w : L2Space) (A w)).re := by
    nlinarith only [hshift]
  have hsum : ‖a‖ ^ 2 + ‖c‖ ^ 2 = 1 := by
    rw [hunit] at hnorm
    simpa using hnorm.symm
  let M := max E (inner ℂ (w : L2Space) (A w)).re
  rw [henergy]
  calc
    _ ≤ ‖a‖ ^ 2 * M + ‖c‖ ^ 2 * M :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))
    _ = M := by rw [← add_mul, hsum, one_mul]

/-- Every unit vector orthogonal to a ground eigenvector has energy at least
the second min-max level. -/
theorem operatorSecondMinmax_le_orthogonal_unit_energy
    {A : L2Space →ₗ.[ℂ] L2Space} (hA : IsSelfAdjoint A)
    {E : ℝ} (v : A.domain) (hv : ‖(v : L2Space)‖ = 1)
    (heig : A v = (E : ℂ) • (v : L2Space))
    (hlower : ∀ u : A.domain,
      E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re)
    (w : A.domain) (hw : ‖(w : L2Space)‖ = 1)
    (horth : inner ℂ (v : L2Space) (w : L2Space) = 0) :
    operatorSecondMinmax A ≤ (inner ℂ (w : L2Space) (A w)).re := by
  have hground := hlower w
  simp only [hw, one_pow, mul_one] at hground
  have hm := max_operatorEnergy_mem_secondUpperBounds hA v w hv hw heig horth
  rw [max_eq_right hground] at hm
  exact csInf_le (operatorSecondUpperBounds_bddBelow hlower) hm

/-- The elementary min-max argument gives the full complement inequality.
No discreteness or existence of a second eigenvector is required. -/
theorem operatorSecondMinmax_complement_lower_bound
    {A : L2Space →ₗ.[ℂ] L2Space} (hA : IsSelfAdjoint A)
    {E : ℝ} (v : A.domain) (hv : ‖(v : L2Space)‖ = 1)
    (heig : A v = (E : ℂ) • (v : L2Space))
    (hlower : ∀ u : A.domain,
      E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re)
    (u : A.domain) (horth : inner ℂ (v : L2Space) (u : L2Space) = 0) :
    operatorSecondMinmax A * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (A u)).re := by
  by_cases hu : (u : L2Space) = 0
  · simp [hu]
  have hn : 0 < ‖(u : L2Space)‖ := norm_pos_iff.mpr hu
  let a : ℂ := (‖(u : L2Space)‖⁻¹ : ℝ)
  let w : A.domain := a • u
  have hw : ‖(w : L2Space)‖ = 1 := by
    change ‖a • (u : L2Space)‖ = 1
    simp only [a, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hworth : inner ℂ (v : L2Space) (w : L2Space) = 0 := by
    change inner ℂ (v : L2Space) (a • (u : L2Space)) = 0
    rw [inner_smul_right, horth, mul_zero]
  have h := operatorSecondMinmax_le_orthogonal_unit_energy hA v hv heig hlower w hw hworth
  rw [show w = a • u from rfl, operatorEnergy_smul] at h
  simp only [a, Complex.norm_real, norm_inv, norm_norm] at h
  have hquot : operatorSecondMinmax A ≤
      (inner ℂ (u : L2Space) (A u)).re / ‖(u : L2Space)‖ ^ 2 := by
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using h
  exact (le_div_iff₀ (sq_pos_of_pos hn)).mp hquot

/-- A bounded-below Rayleigh infimum bounds the form on the entire domain.
The proof normalizes each nonzero vector and then uses quadratic homogeneity. -/
theorem operatorVariationalBottom_lower_bound
    (A : L2Space →ₗ.[ℂ] L2Space)
    (hbelow : BddBelow {r : ℝ | ∃ u : A.domain, ‖(u : L2Space)‖ = 1 ∧
      (inner ℂ (u : L2Space) (A u)).re = r}) (u : A.domain) :
    operatorVariationalBottom A * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (A u)).re := by
  by_cases hu : (u : L2Space) = 0
  · simp [hu]
  have hn : 0 < ‖(u : L2Space)‖ := norm_pos_iff.mpr hu
  let a : ℂ := (‖(u : L2Space)‖⁻¹ : ℝ)
  let w : A.domain := a • u
  have hw : ‖(w : L2Space)‖ = 1 := by
    change ‖a • (u : L2Space)‖ = 1
    simp only [a, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have h : operatorVariationalBottom A ≤ (inner ℂ (w : L2Space) (A w)).re :=
    csInf_le hbelow ⟨w, hw, rfl⟩
  rw [show w = a • u from rfl, operatorEnergy_smul] at h
  simp only [a, Complex.norm_real, norm_inv, norm_norm] at h
  have hquot : operatorVariationalBottom A ≤
      (inner ℂ (u : L2Space) (A u)).re / ‖(u : L2Space)‖ ^ 2 := by
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using h
  exact (le_div_iff₀ (sq_pos_of_pos hn)).mp hquot

/-- A positive separation between the first two min-max levels produces the
certificate used by the one-well construction. Its complement estimate is
proved above from the defining two-dimensional variational principle. -/
def groundStateCertificate_of_secondMinmax
    {A : L2Space →ₗ.[ℂ] L2Space} (hA : IsSelfAdjoint A)
    {E : ℝ} (v : A.domain) (hv : ‖(v : L2Space)‖ = 1)
    (heig : A v = (E : ℂ) • (v : L2Space))
    (hlower : ∀ u : A.domain,
      E * ‖(u : L2Space)‖ ^ 2 ≤ (inner ℂ (u : L2Space) (A u)).re)
    (hgap : E < operatorSecondMinmax A) : GroundStateCertificate A E where
  vector := v
  vector_ne_zero := by intro h; simp [h] at hv
  eigenvector := heig
  lower_bound := hlower
  gap := operatorSecondMinmax A - E
  gap_pos := sub_pos.mpr hgap
  gap_bound := by
    intro u horth
    simpa only [add_sub_cancel] using
      operatorSecondMinmax_complement_lower_bound hA v hv heig hlower u horth

end InfiniteZero
