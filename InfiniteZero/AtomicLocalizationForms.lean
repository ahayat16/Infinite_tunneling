import InfiniteZero.AtomicLocalizationEnergy
import InfiniteZero.AtomicLocalizationOverlap
import InfiniteZero.MagneticIMSIntegrated

/-!
# Fixed atomic localization on the test-function form

The inner form is exactly the reference radial form, the exterior form has
a fixed positive reserve, and the IMS loss is bounded independently of the
coupling. The final lemma transfers a reference radial gap to a lower bound
for the concrete nonradial potential. It does not assert the radial input,
construct a ground state, or extend the bound to the closed operator domain.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem atomicInnerCutoff_form_eq_core {p : CuspParameters} (hp : p.BasicConditions)
    (coupling : ℝ) (ψ : Wavefunction) :
    magneticForm p.b coupling p.potential
      (fun x => (p.atomicInnerCutoff hp.r₀_pos x : ℂ) * ψ x) =
    magneticForm p.b coupling p.core
      (fun x => (p.atomicInnerCutoff hp.r₀_pos x : ℂ) * ψ x) := by
  simp only [magneticForm_eq_integral_density]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (atomicInnerCutoff_energyDensity_eq_core hp coupling ψ)

theorem atomicOuterCutoff_form_lower {p : CuspParameters} (hp : p.BasicConditions)
    {e : ℝ} (he : e ≤ -(3 / 4 : ℝ)) (coupling : ℝ)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    coupling ^ 2 / 4 * mass (fun x => (p.atomicOuterCutoff hp.r₀_pos x : ℂ) * ψ x) ≤
      magneticForm p.b coupling p.potential
        (fun x => (p.atomicOuterCutoff hp.r₀_pos x : ℂ) * ψ x) -
      coupling ^ 2 * e * mass (fun x => (p.atomicOuterCutoff hp.r₀_pos x : ℂ) * ψ x) := by
  have hu := hψ.real_mul (p.atomicOuterCutoff_contDiff hp.r₀_pos)
  have hform := hu.integrable_magneticEnergyDensity p.b coupling
    (potential_contDiff hp).continuous
  have hm := hu.integrable_norm_sq
  have hi := integral_mono (hm.const_mul (coupling ^ 2 / 4))
    (hform.sub (hm.const_mul (coupling ^ 2 * e)))
    (atomicOuterCutoff_energyDensity_lower hp he coupling ψ)
  simpa only [Pi.sub_apply, integral_const_mul,
    integral_sub hform (hm.const_mul (coupling ^ 2 * e)),
    magneticForm_eq_integral_density, mass] using hi

theorem integral_atomicIMSError_le {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {C : ℝ} (hC : ∀ x, magneticIMSError (p.atomicInnerCutoff hr₀)
      (p.atomicOuterCutoff hr₀) x ≤ C) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    (∫ x : Plane, magneticIMSError (p.atomicInnerCutoff hr₀)
      (p.atomicOuterCutoff hr₀) x * ‖ψ x‖ ^ 2) ≤ C * mass ψ := by
  have hi := integral_mono
    (hψ.integrable_magneticIMSError (p.atomicInnerCutoff_contDiff hr₀)
      (p.atomicOuterCutoff_contDiff hr₀))
    (hψ.integrable_norm_sq.const_mul C)
    (fun x => mul_le_mul_of_nonneg_right (hC x) (sq_nonneg ‖ψ x‖))
  simpa only [integral_const_mul, mass] using hi

theorem core_exteriorMass_le_test {p : CuspParameters} (hr₀ : 0 < p.r₀)
    (b coupling : ℝ) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    coupling ^ 2 * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖ψ x‖ ^ 2) ≤
      magneticForm b coupling p.core ψ + coupling ^ 2 * mass ψ :=
  core_exteriorMass_le (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2)
    (hψ.integrable_magneticEnergyDensity b coupling (core_contDiff hr₀).continuous)

/-- All localization losses are proved for the actual cusp potential. The
only spectral input in this lemma is the displayed reference radial form gap.
The exterior mass is an actual integral, not an assumed source coefficient. -/
theorem atomic_test_complement_lower {p : CuspParameters} (hp : p.BasicConditions)
    {coupling e g C : ℝ} (he : e ≤ -(3 / 4 : ℝ)) (hg : 0 ≤ g)
    (hgUpper : g ≤ coupling ^ 2 / 4)
    (hC : ∀ x, magneticIMSError (p.atomicInnerCutoff hp.r₀_pos)
      (p.atomicOuterCutoff hp.r₀_pos) x ≤ C)
    {φ ψ : Wavefunction} (hφ : MemLp φ 2 volume) (hψ : IsTestFunction ψ)
    (horth : waveInner φ ψ = 0)
    (hgap : ∀ u : Wavefunction, IsTestFunction u →
      g * (mass u - ‖waveInner φ u‖ ^ 2) ≤
        magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) :
    (g - g * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - C) * mass ψ ≤
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
  have ho : ‖waveInner φ u₀‖ ^ 2 ≤ mext * mass ψ :=
    norm_waveInner_atomicInnerCutoff_sq_le_exterior_mass hp.r₀_pos hφ
      (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2) horth
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
  change (g - g * mext - C) * mass ψ ≤ _
  calc
    _ = g * (mass u₀ - mext * mass ψ) + g * mass u₁ - C * mass ψ := by
      nlinarith only [congrArg (fun z : ℝ => g * z) hm]
    _ ≤ g * (mass u₀ - ‖waveInner φ u₀‖ ^ 2) + g * mass u₁ - err := by
      have hw := mul_le_mul_of_nonneg_left ho hg
      linarith
    _ ≤ (magneticForm p.b coupling p.core u₀ - coupling ^ 2 * e * mass u₀) +
        (magneticForm p.b coupling p.potential u₁ - coupling ^ 2 * e * mass u₁) - err :=
      sub_le_sub_right (add_le_add h₀ h₁) err
    _ = _ := hi.symm

/-- The full constructed potential inherits a positive order-coupling
complement bound from radial reference data. The inputs concern only `p.core`:
normalization, finite form energy, its O(coupling) energy excess, and its gap.
No nonradial gap, Agmon bound or exponential orthogonality estimate is assumed.
This theorem is still on tests; the radial inputs and closed-domain transfer
are separate obligations. -/
theorem exists_atomic_test_coercivity_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ (e : ℝ) (φ : Wavefunction),
      MemLp φ 2 volume → mass φ = 1 →
      Integrable (magneticEnergyDensity p.b coupling p.core φ) →
      magneticForm p.b coupling p.core φ = coupling ^ 2 * e →
      e ≤ -1 + B / coupling →
      (∀ u : Wavefunction, IsTestFunction u →
        (γ * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) →
      ∀ ψ : Wavefunction, IsTestFunction ψ → waveInner φ ψ = 0 →
        (γ / 2 * coupling) * mass ψ ≤
          magneticForm p.b coupling p.potential ψ - coupling ^ 2 * e * mass ψ := by
  obtain ⟨C, hC, herror⟩ := exists_atomicIMSError_bound p hp.r₀_pos
  let T := max 1 (max (4 * B) (max (4 * γ) (2 * (γ * B + C) / γ)))
  refine ⟨T, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro coupling hcoupling e φ hφ hmass hform henergy he hgap ψ hψ horth
  change max 1 (max (4 * B) (max (4 * γ) (2 * (γ * B + C) / γ))) ≤ coupling at hcoupling
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
  have hweighted := mul_le_mul_of_nonneg_left hmext (mul_nonneg hγ.le hCoupling.le)
  have hcancel : γ * coupling * (B / coupling) = γ * B := by field_simp
  rw [hcancel] at hweighted
  have habsorb := (div_le_iff₀ hγ).mp hCouplingC
  have hcoefficient : γ / 2 * coupling ≤ γ * coupling -
      (γ * coupling) * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - C := by
    nlinarith only [hweighted, habsorb]
  apply (mul_le_mul_of_nonneg_right hcoefficient (mass_nonneg ψ)).trans
  apply atomic_test_complement_lower hp he' (mul_nonneg hγ.le hCoupling.le) _ herror hφ hψ horth hgap
  nlinarith only [mul_le_mul_of_nonneg_right hCouplingGamma hCoupling.le]

end InfiniteZero.CuspParameters
