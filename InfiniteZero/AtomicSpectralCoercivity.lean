import InfiniteZero.AtomicExteriorGraph
import InfiniteZero.AtomicLocalizationRankOne
import InfiniteZero.MagneticGraphLowerBound

/-!
# Atomic coercivity from purely spectral radial data

The only radial inputs are a normalized ground state, its order-coupling
energy excess, and a gap on tests. Exterior probability is deduced from the
closed radial graph. No integrability or form-energy identity is assumed
for that noncompact ground state.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero.CuspParameters

/-- A uniform rank-one test bound, with no noncompact form hypothesis. -/
theorem exists_atomic_spectral_test_rankOne_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsMagneticRealization p.b coupling p.core → ∀ φ : Wavefunction,
      IsAtomicGroundState p.b p.core coupling φ →
      let e := (coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling
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
  intro coupling hcoupling hA φ hφ e he hgap ψ hψ
  change max 1 (max (4 * B) (max (4 * γ) (2 * (2 * γ * B + C) / γ))) ≤ coupling at hcoupling
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
  apply (sub_le_sub_right (mul_le_mul_of_nonneg_right hcoefficient (mass_nonneg ψ)) _).trans
  apply atomic_test_rankOne_lower hp he' (mul_nonneg hγ.le hCoupling.le) _
    herror hφ.1.2.1 hψ hgap
  nlinarith only [mul_le_mul_of_nonneg_right hCouplingGamma hCoupling.le]

/-- The same rank-one bound on the actual full-potential operator domain. -/
theorem exists_atomic_spectral_operator_rankOne_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsMagneticRealization p.b coupling p.core →
      IsMagneticRealization p.b coupling p.potential → ∀ φ : Wavefunction,
      ∀ hφ : IsAtomicGroundState p.b p.core coupling φ,
      let e := (coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling
      e ≤ -1 + B / coupling →
      (∀ u : Wavefunction, IsTestFunction u →
        (γ * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) →
      ∀ u : (magneticOperator p.b coupling p.potential).domain,
        (γ / 2 * coupling) * ‖(u : L2Space)‖ ^ 2 -
          2 * (γ * coupling) * ‖inner ℂ (hφ.1.2.1.toLp φ) (u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space) (magneticOperator p.b coupling p.potential u)).re -
          coupling ^ 2 * e * ‖(u : L2Space)‖ ^ 2 := by
  obtain ⟨T, hT, hbound⟩ := exists_atomic_spectral_test_rankOne_threshold hp hγ B
  refine ⟨T, hT, ?_⟩
  intro coupling hc hAcore hApot φ hφ e hupper hgap u
  exact hApot.rankOne_lower (potential_contDiff hp).continuous hφ.1.2.1
    (hbound coupling hc hAcore φ hφ hupper hgap) u

/-- Coercivity on the radial state's orthogonal complement, now requiring only
spectral radial data and the two classical graph-realization certificates. -/
theorem exists_atomic_spectral_operator_complement_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsMagneticRealization p.b coupling p.core →
      IsMagneticRealization p.b coupling p.potential → ∀ φ : Wavefunction,
      ∀ hφ : IsAtomicGroundState p.b p.core coupling φ,
      let e := (coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling
      e ≤ -1 + B / coupling →
      (∀ u : Wavefunction, IsTestFunction u →
        (γ * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) →
      ∀ u : (magneticOperator p.b coupling p.potential).domain,
        inner ℂ (hφ.1.2.1.toLp φ) (u : L2Space) = 0 →
        (coupling ^ 2 * e + γ / 2 * coupling) * ‖(u : L2Space)‖ ^ 2 ≤
          (inner ℂ (u : L2Space) (magneticOperator p.b coupling p.potential u)).re := by
  obtain ⟨T, hT, hbound⟩ := exists_atomic_spectral_test_rankOne_threshold hp hγ B
  refine ⟨T, hT, ?_⟩
  intro coupling hc hAcore hApot φ hφ e hupper hgap u horth
  exact hApot.complement_lower (potential_contDiff hp).continuous hφ.1.2.1
    (hbound coupling hc hAcore φ hφ hupper hgap) u horth

end InfiniteZero.CuspParameters
