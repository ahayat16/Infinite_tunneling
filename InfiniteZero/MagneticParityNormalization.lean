import InfiniteZero.MagneticParityGraphLowerBound
import InfiniteZero.ParityTrialStates
import InfiniteZero.AtomicLocalizationOverlap

/-!
# Normalization and nonemptiness of the parity test core

Quadratic homogeneity extends bounds on unit tests to every test. Combined
with the projected closed-graph argument, a nonzero parity-domain vector
forces the existence of a normalized parity test. Thus later parity
infima need no extra nonemptiness assumption.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem HasParity.smul {even : Bool} {ψ : Wavefunction}
    (hp : HasParity even ψ) (c : ℂ) : HasParity even (c • ψ) := by
  intro x
  simp only [Pi.smul_apply, hp x]
  cases even <;> simp

theorem magneticForm_smul (b coupling : ℝ) (V : Potential)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) (c : ℂ) :
    magneticForm b coupling V (c • ψ) = ‖c‖ ^ 2 * magneticForm b coupling V ψ := by
  simp only [magneticForm, covariantDerivative_smul b coupling _
    (hψ.1.differentiable (by simp)), Pi.smul_apply, norm_smul, mul_pow]
  have heq : (fun x : Plane =>
      (∑ i : Fin 2, ‖c‖ ^ 2 * ‖covariantDerivative b coupling i ψ x‖ ^ 2) +
        coupling ^ 2 * V x * (‖c‖ ^ 2 * ‖ψ x‖ ^ 2)) =
      fun x => ‖c‖ ^ 2 * ((∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2) +
        coupling ^ 2 * V x * ‖ψ x‖ ^ 2) := by
    funext x
    rw [← Finset.mul_sum]
    ring
  rw [heq, integral_const_mul]

theorem IsTestFunction.eq_zero_of_mass_eq_zero {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) (hm : mass ψ = 0) : ψ = 0 := by
  have hn := norm_toLp_sq_eq_mass hψ.memLp
  rw [hm] at hn
  have hz : hψ.memLp.toLp ψ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hae : ψ =ᵐ[volume] (0 : Wavefunction) :=
    hψ.memLp.coeFn_toLp.symm.trans (hz ▸ Lp.coeFn_zero ℂ 2 volume)
  exact Measure.eq_of_ae_eq hae hψ.1.continuous continuous_const

theorem parity_test_lower_of_normalized {b coupling E : ℝ} {V : Potential}
    (even : Bool)
    (hbound : ∀ ψ : Wavefunction, IsNormalizedTest ψ → HasParity even ψ →
      E ≤ magneticForm b coupling V ψ)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) (hp : HasParity even ψ) :
    E * mass ψ ≤ magneticForm b coupling V ψ := by
  by_cases hm : mass ψ = 0
  · rw [hψ.eq_zero_of_mass_eq_zero hm]
    simp [magneticForm, mass]
  have hmpos : 0 < mass ψ := lt_of_le_of_ne (mass_nonneg ψ) (Ne.symm hm)
  let r : ℝ := (Real.sqrt (mass ψ))⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hmpos)
  have hnorm : mass ((r : ℂ) • ψ) = 1 := by
    rw [mass_smul_wavefunction, Complex.norm_real, Real.norm_of_nonneg hr.le]
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt hmpos.le, inv_mul_cancel₀ hm]
  have h := hbound ((r : ℂ) • ψ) ⟨hψ.smul _, hnorm⟩ (hp.smul _)
  rw [magneticForm_smul b coupling V hψ, Complex.norm_real, Real.norm_of_nonneg hr.le] at h
  have hrmass : r ^ 2 * mass ψ = 1 := by
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt hmpos.le, inv_mul_cancel₀ hm]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
  calc
    r ^ 2 * (E * mass ψ) = E * (r ^ 2 * mass ψ) := by ring
    _ = E := by rw [hrmass, mul_one]
    _ ≤ r ^ 2 * magneticForm b coupling V ψ := h

theorem IsMagneticRealization.parity_lower_of_normalized_test
    {b coupling L E : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) (even : Bool)
    (hbound : ∀ ψ : Wavefunction, IsNormalizedTest ψ → HasParity even ψ →
      E ≤ magneticForm b coupling (doubleWellPotential v L) ψ)
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : HasL2Parity even (u : L2Space)) :
    E * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space)
        (magneticOperator b coupling (doubleWellPotential v L) u)).re :=
  hA.parity_lower_of_test hV even
    (fun _ hψ hp => parity_test_lower_of_normalized even hbound hψ hp) u hu

theorem IsMagneticRealization.exists_normalized_parity_test_of_domain_vector
    {b coupling L : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L)) (even : Bool)
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : HasL2Parity even (u : L2Space)) (hu0 : (u : L2Space) ≠ 0) :
    ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ := by
  by_contra hnone
  let e := (inner ℂ (u : L2Space)
    (magneticOperator b coupling (doubleWellPotential v L) u)).re
  have hnorm : 0 < ‖(u : L2Space)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu0)
  have h := hA.parity_lower_of_normalized_test hV even
    (E := (e + ‖(u : L2Space)‖ ^ 2) / ‖(u : L2Space)‖ ^ 2)
    (fun ψ hψ hp => False.elim (hnone ⟨ψ, hψ, hp⟩)) u hu
  rw [div_mul_cancel₀ _ hnorm.ne'] at h
  change e + ‖(u : L2Space)‖ ^ 2 ≤ e at h
  linarith

end InfiniteZero
