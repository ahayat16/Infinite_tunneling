import InfiniteZero.AtomicLocalizationForms

/-!
# A rank-one lower form bound for the constructed potential

Keeping the reference-state overlap gives an inequality on every test
function. This can be transferred by continuity to the closed graph without
assuming that orthogonal test functions form a core for a compression.
Only the displayed radial reference data remain inputs.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem atomic_test_rankOne_lower {p : CuspParameters} (hp : p.BasicConditions)
    {coupling e g C : ℝ} (he : e ≤ -(3 / 4 : ℝ)) (hg : 0 ≤ g)
    (hgUpper : g ≤ coupling ^ 2 / 4)
    (hC : ∀ x, magneticIMSError (p.atomicInnerCutoff hp.r₀_pos)
      (p.atomicOuterCutoff hp.r₀_pos) x ≤ C)
    {φ ψ : Wavefunction} (hφ : MemLp φ 2 volume) (hψ : IsTestFunction ψ)
    (hgap : ∀ u : Wavefunction, IsTestFunction u →
      g * (mass u - ‖waveInner φ u‖ ^ 2) ≤
        magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) :
    (g - 2 * g * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - C) * mass ψ -
      2 * g * ‖waveInner φ ψ‖ ^ 2 ≤
      magneticForm p.b coupling p.potential ψ - coupling ^ 2 * e * mass ψ := by
  let u₀ : Wavefunction := fun x => (p.atomicInnerCutoff hp.r₀_pos x : ℂ) * ψ x
  let u₁ : Wavefunction := fun x => (p.atomicOuterCutoff hp.r₀_pos x : ℂ) * ψ x
  let mext := ∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2
  let err := ∫ x : Plane, magneticIMSError (p.atomicInnerCutoff hp.r₀_pos)
    (p.atomicOuterCutoff hp.r₀_pos) x * ‖ψ x‖ ^ 2
  have h₀ := hgap u₀ (hψ.real_mul (p.atomicInnerCutoff_contDiff hp.r₀_pos))
  have h₁ : g * mass u₁ ≤ magneticForm p.b coupling p.potential u₁ -
      coupling ^ 2 * e * mass u₁ :=
    (mul_le_mul_of_nonneg_right hgUpper (mass_nonneg u₁)).trans
      (atomicOuterCutoff_form_lower hp he coupling hψ)
  have ho : ‖waveInner φ u₀‖ ^ 2 ≤
      2 * ‖waveInner φ ψ‖ ^ 2 + 2 * mext * mass ψ :=
    norm_waveInner_atomicInnerCutoff_sq_le_overlap_exterior_mass hp.r₀_pos hφ
      (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2)
  have he' : err ≤ C * mass ψ := integral_atomicIMSError_le hp.r₀_pos hC hψ
  have hm : mass u₀ + mass u₁ = mass ψ :=
    mass_ims hψ (p.atomicInnerCutoff_contDiff hp.r₀_pos)
      (p.atomicOuterCutoff_contDiff hp.r₀_pos) (p.atomicCutoffs_partition hp.r₀_pos)
  have hi := magneticForm_sub_mass_ims p.b coupling (coupling ^ 2 * e)
    (potential_contDiff hp).continuous hψ (p.atomicInnerCutoff_contDiff hp.r₀_pos)
    (p.atomicOuterCutoff_contDiff hp.r₀_pos) (p.atomicCutoffs_partition hp.r₀_pos)
  rw [atomicInnerCutoff_form_eq_core hp] at hi
  change magneticForm p.b coupling p.potential ψ - coupling ^ 2 * e * mass ψ =
    (magneticForm p.b coupling p.core u₀ - coupling ^ 2 * e * mass u₀) +
    (magneticForm p.b coupling p.potential u₁ - coupling ^ 2 * e * mass u₁) - err at hi
  change (g - 2 * g * mext - C) * mass ψ - 2 * g * ‖waveInner φ ψ‖ ^ 2 ≤ _
  calc
    _ = g * (mass u₀ - (2 * ‖waveInner φ ψ‖ ^ 2 + 2 * mext * mass ψ)) +
        g * mass u₁ - C * mass ψ := by
      nlinarith only [congrArg (fun z : ℝ => g * z) hm]
    _ ≤ g * (mass u₀ - ‖waveInner φ u₀‖ ^ 2) + g * mass u₁ - err := by
      have hw := mul_le_mul_of_nonneg_left ho hg
      linarith
    _ ≤ (magneticForm p.b coupling p.core u₀ - coupling ^ 2 * e * mass u₀) +
        (magneticForm p.b coupling p.potential u₁ - coupling ^ 2 * e * mass u₁) - err :=
      sub_le_sub_right (add_le_add h₀ h₁) err
    _ = _ := hi.symm

/-- The threshold is chosen before the coupling, radial state and test
function. No orthogonality or nonradial spectral input is required. -/
theorem exists_atomic_test_rankOne_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ (e : ℝ) (φ : Wavefunction),
      MemLp φ 2 volume → mass φ = 1 →
      Integrable (magneticEnergyDensity p.b coupling p.core φ) →
      magneticForm p.b coupling p.core φ = coupling ^ 2 * e →
      e ≤ -1 + B / coupling →
      (∀ u : Wavefunction, IsTestFunction u →
        (γ * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) →
      ∀ ψ : Wavefunction, IsTestFunction ψ →
        (γ / 2 * coupling) * mass ψ - 2 * (γ * coupling) * ‖waveInner φ ψ‖ ^ 2 ≤
          magneticForm p.b coupling p.potential ψ - coupling ^ 2 * e * mass ψ := by
  obtain ⟨C, hC, herror⟩ := exists_atomicIMSError_bound p hp.r₀_pos
  let T := max 1 (max (4 * B) (max (4 * γ) (2 * (2 * γ * B + C) / γ)))
  refine ⟨T, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro coupling hcoupling e φ hφ hmass hform henergy he hgap ψ hψ
  change max 1 (max (4 * B) (max (4 * γ) (2 * (2 * γ * B + C) / γ))) ≤ coupling at hcoupling
  rcases max_le_iff.mp hcoupling with ⟨hCoupling1, hrest⟩
  rcases max_le_iff.mp hrest with ⟨hCouplingB, hrest⟩
  rcases max_le_iff.mp hrest with ⟨hCouplingGamma, hCouplingC⟩
  have hCoupling : 0 < coupling := lt_of_lt_of_le zero_lt_one hCoupling1
  have he' : e ≤ -(3 / 4 : ℝ) := by
    have hratio : B / coupling ≤ 1 / 4 :=
      (div_le_iff₀ hCoupling).mpr (by linarith)
    linarith
  have hupper : magneticForm p.b coupling p.core φ ≤
      (-coupling ^ 2 + B * coupling) * mass φ := by
    rw [henergy, hmass, mul_one]
    calc
      _ ≤ coupling ^ 2 * (-1 + B / coupling) :=
        mul_le_mul_of_nonneg_left he (sq_nonneg coupling)
      _ = _ := by field_simp
  have hmext := core_exteriorMass_le_of_energy_upper hCoupling hφ hform hupper
  rw [hmass, mul_one] at hmext
  have hweighted := mul_le_mul_of_nonneg_left hmext
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ.le) hCoupling.le)
  have hcancel : 2 * γ * coupling * (B / coupling) = 2 * γ * B := by field_simp
  rw [hcancel] at hweighted
  have habsorb := (div_le_iff₀ hγ).mp hCouplingC
  have hcoefficient : γ / 2 * coupling ≤ γ * coupling -
      2 * (γ * coupling) * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - C := by
    nlinarith only [hweighted, habsorb]
  apply (sub_le_sub_right (mul_le_mul_of_nonneg_right hcoefficient (mass_nonneg ψ)) _).trans
  apply atomic_test_rankOne_lower hp he' (mul_nonneg hγ.le hCoupling.le) _ herror hφ hψ hgap
  nlinarith only [mul_le_mul_of_nonneg_right hCouplingGamma hCoupling.le]

end InfiniteZero.CuspParameters
