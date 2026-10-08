import InfiniteZero.AtomicSpectralCoercivity
import InfiniteZero.RadialCoreSpectralData
import InfiniteZero.RadialCoreGroundChoice

/-!
# Atomic test coercivity with a localized weight penalty

A continuous penalty bounded by `coupling² / 8` times the exterior cutoff
squared can be absorbed while retaining the order-coupling rank-one bound.
The threshold and the reference state are chosen before the penalty. All
integrals involving a test follow from its compact support; no form-domain
assumption is imposed on the noncompact radial ground state.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero.CuspParameters

theorem integral_atomic_penalty_le_outer_mass {p : CuspParameters}
    (hr₀ : 0 < p.r₀) {coupling : ℝ} {P : Potential} (hP : Continuous P)
    (hPpoint : ∀ x, P x ≤ coupling ^ 2 / 8 * (p.atomicOuterCutoff hr₀ x) ^ 2)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    (∫ x : Plane, P x * ‖ψ x‖ ^ 2) ≤ coupling ^ 2 / 8 *
      mass (fun x => (p.atomicOuterCutoff hr₀ x : ℂ) * ψ x) := by
  have hi : Integrable (fun x => P x * ‖ψ x‖ ^ 2) := by
    apply (hP.mul (hψ.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    exact (hψ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mul_left
  have hout := (hψ.real_mul (p.atomicOuterCutoff_contDiff hr₀)).integrable_norm_sq
  have h := integral_mono hi (hout.const_mul (coupling ^ 2 / 8)) (fun x => ?_)
  · simpa only [integral_const_mul, mass] using h
  · simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      mul_assoc] using mul_le_mul_of_nonneg_right (hPpoint x) (sq_nonneg ‖ψ x‖)

theorem atomic_test_rankOne_lower_sub_penalty {p : CuspParameters}
    (hp : p.BasicConditions) {coupling e g C : ℝ}
    (he : e ≤ -(3 / 4 : ℝ)) (hg : 0 ≤ g) (hgUpper : g ≤ coupling ^ 2 / 8)
    (hC : ∀ x, magneticIMSError (p.atomicInnerCutoff hp.r₀_pos)
      (p.atomicOuterCutoff hp.r₀_pos) x ≤ C)
    {φ ψ : Wavefunction} (hφ : MemLp φ 2 volume) (hψ : IsTestFunction ψ)
    (hgap : ∀ u : Wavefunction, IsTestFunction u →
      g * (mass u - ‖waveInner φ u‖ ^ 2) ≤
        magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u)
    {P : Potential} (hP : Continuous P)
    (hPpoint : ∀ x, P x ≤ coupling ^ 2 / 8 * (p.atomicOuterCutoff hp.r₀_pos x) ^ 2) :
    (g - 2 * g * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - C) * mass ψ -
      2 * g * ‖waveInner φ ψ‖ ^ 2 ≤
      magneticForm p.b coupling p.potential ψ - coupling ^ 2 * e * mass ψ -
        ∫ x : Plane, P x * ‖ψ x‖ ^ 2 := by
  let u₀ : Wavefunction := fun x => (p.atomicInnerCutoff hp.r₀_pos x : ℂ) * ψ x
  let u₁ : Wavefunction := fun x => (p.atomicOuterCutoff hp.r₀_pos x : ℂ) * ψ x
  let mext := ∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2
  let err := ∫ x : Plane, magneticIMSError (p.atomicInnerCutoff hp.r₀_pos)
    (p.atomicOuterCutoff hp.r₀_pos) x * ‖ψ x‖ ^ 2
  let penalty := ∫ x : Plane, P x * ‖ψ x‖ ^ 2
  have h₀ := hgap u₀ (hψ.real_mul (p.atomicInnerCutoff_contDiff hp.r₀_pos))
  have h₁ : g * mass u₁ ≤ magneticForm p.b coupling p.potential u₁ -
      coupling ^ 2 * e * mass u₁ - penalty := by
    have hp' := integral_atomic_penalty_le_outer_mass hp.r₀_pos hP hPpoint hψ
    have hg' := mul_le_mul_of_nonneg_right hgUpper (mass_nonneg u₁)
    have hout := atomicOuterCutoff_form_lower hp he coupling hψ
    change penalty ≤ coupling ^ 2 / 8 * mass u₁ at hp'
    change coupling ^ 2 / 4 * mass u₁ ≤
      magneticForm p.b coupling p.potential u₁ - coupling ^ 2 * e * mass u₁ at hout
    linarith only [hp', hg', hout]
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
  change (g - 2 * g * mext - C) * mass ψ - 2 * g * ‖waveInner φ ψ‖ ^ 2 ≤
    magneticForm p.b coupling p.potential ψ - coupling ^ 2 * e * mass ψ - penalty
  have hw := mul_le_mul_of_nonneg_left ho hg
  have hm' := congrArg (fun z : ℝ => g * z) hm
  nlinarith only [h₀, h₁, he', hw, hm', hi]

/-- The uniform threshold allows every continuous admissible penalty after
the coupling and radial state have been fixed. Only spectral radial data are
used; no integrability of the radial state's differential energy is assumed. -/
theorem exists_atomic_spectral_test_rankOne_penalty_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsMagneticRealization p.b coupling p.core → ∀ φ : Wavefunction,
      IsAtomicGroundState p.b p.core coupling φ →
      let e := (coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling
      e ≤ -1 + B / coupling →
      (∀ u : Wavefunction, IsTestFunction u →
        (γ * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) →
      ∀ P : Potential, Continuous P →
      (∀ x, P x ≤ coupling ^ 2 / 8 * (p.atomicOuterCutoff hp.r₀_pos x) ^ 2) →
      ∀ ψ : Wavefunction, IsTestFunction ψ →
        (γ / 2 * coupling) * mass ψ - 2 * (γ * coupling) * ‖waveInner φ ψ‖ ^ 2 ≤
          magneticForm p.b coupling p.potential ψ -
            atomicGroundEnergy p.b p.core coupling * mass ψ -
            ∫ x : Plane, P x * ‖ψ x‖ ^ 2 := by
  obtain ⟨C, _, herror⟩ := exists_atomicIMSError_bound p hp.r₀_pos
  let T := max 1 (max (4 * B) (max (8 * γ) (2 * (2 * γ * B + C) / γ)))
  refine ⟨T, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro coupling hcoupling hA φ hφ e he hgap P hP hPpoint ψ hψ
  change max 1 (max (4 * B) (max (8 * γ) (2 * (2 * γ * B + C) / γ))) ≤ coupling at hcoupling
  rcases max_le_iff.mp hcoupling with ⟨hCoupling1, hrest⟩
  rcases max_le_iff.mp hrest with ⟨hCouplingB, hrest⟩
  rcases max_le_iff.mp hrest with ⟨hCouplingGamma, hCouplingC⟩
  have hCoupling : 0 < coupling := lt_of_lt_of_le zero_lt_one hCoupling1
  have he' : e ≤ -(3 / 4 : ℝ) := by
    have hratio : B / coupling ≤ 1 / 4 :=
      (div_le_iff₀ hCoupling).mpr (by linarith)
    linarith
  have hmext := core_exteriorMass_le_of_atomicGroundState hp.r₀_pos hCoupling hA hφ he
  have hweighted := mul_le_mul_of_nonneg_left hmext
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ.le) hCoupling.le)
  have hcancel : 2 * γ * coupling * (B / coupling) = 2 * γ * B := by field_simp
  rw [hcancel] at hweighted
  have habsorb := (div_le_iff₀ hγ).mp hCouplingC
  have hcoefficient : γ / 2 * coupling ≤ γ * coupling -
      2 * (γ * coupling) * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - C := by
    nlinarith only [hweighted, habsorb]
  have hgUpper : γ * coupling ≤ coupling ^ 2 / 8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hCouplingGamma hCoupling.le]
  have hbound := atomic_test_rankOne_lower_sub_penalty hp he'
    (mul_nonneg hγ.le hCoupling.le) hgUpper herror hφ.1.2.1 hψ hgap hP hPpoint
  have henergy : coupling ^ 2 * e = atomicGroundEnergy p.b p.core coupling := by
    dsimp only [e]
    field_simp
  rw [henergy] at hbound
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_right hcoefficient (mass_nonneg ψ)) _).trans hbound

/-- Choose the genuine radial state before all admissible penalties. -/
theorem exists_atomic_weighted_test_coercivity_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∃ φ : Wavefunction,
      IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
      ∀ P : Potential, Continuous P →
      (∀ x, P x ≤ coupling ^ 2 / 8 * (p.atomicOuterCutoff hp.r₀_pos x) ^ 2) →
      ∀ ψ : Wavefunction, IsTestFunction ψ →
        (hRad.gap / 2 * coupling) * mass ψ -
          2 * (hRad.gap * coupling) * ‖waveInner φ ψ‖ ^ 2 ≤
          magneticForm p.b coupling p.potential ψ -
            atomicGroundEnergy p.b p.core coupling * mass ψ -
            ∫ x : Plane, P x * ‖ψ x‖ ^ 2 := by
  obtain ⟨T, hT, hbound⟩ :=
    exists_atomic_spectral_test_rankOne_penalty_threshold hp hRad.gap_pos hRad.energyBound
  refine ⟨max T hRad.threshold, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcT := (le_max_left T hRad.threshold).trans hc
  have hcRad := (le_max_right T hRad.threshold).trans hc
  obtain ⟨φ, hφ, hpos, hupper, hgap⟩ :=
    hRad.positive_ground_with_gap hp.r₀_pos (hAcore coupling) hcRad
  exact ⟨φ, hφ, hpos, hbound coupling hcT (hAcore coupling) φ hφ hupper hgap⟩

end InfiniteZero.CuspParameters
