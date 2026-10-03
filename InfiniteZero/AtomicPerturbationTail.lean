import InfiniteZero.AtomicPerturbationDomain
import InfiniteZero.ConstructionSupportSeparation
import InfiniteZero.WavefunctionL2Bridge

/-!
# The atomic perturbation is controlled by exterior mass

The actual cusp perturbation vanishes on the ball of radius `4 r₀` and has
absolute value at most `2 ε a`. Its action on any L² vector is therefore
controlled by the mass of a representative outside that ball. Multiplication
by `coupling²` gives the residual in the exact core-to-full graph identity.
No decay estimate or spectral hypothesis is assumed here.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero.CuspParameters

theorem atomicPerturbation_eq_cusps (p : CuspParameters) (x : Plane) :
    p.atomicPerturbation x = p.ε * (p.cuspPlus x + p.cuspMinus x) := by
  simp only [atomicPerturbation, Pi.sub_apply, potential, add_sub_cancel_left]

theorem abs_atomicPerturbation_le_cusp_depth {p : CuspParameters}
    (hp : p.BasicConditions) (x : Plane) :
    |p.atomicPerturbation x| ≤ 2 * p.ε * p.a := by
  have hplus := cuspPlus_range hp x
  have hminus := cuspMinus_range hp x
  have hlower := mul_le_mul_of_nonneg_left
    (show -2 * p.a ≤ p.cuspPlus x + p.cuspMinus x by linarith [hplus.1, hminus.1]) hp.ε_pos.le
  have hupper := mul_nonpos_of_nonneg_of_nonpos hp.ε_pos.le (add_nonpos hplus.2 hminus.2)
  rw [atomicPerturbation_eq_cusps]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_pos hp.ε_pos hp.a_pos]

theorem atomicPerturbation_zero_of_norm_le_four_r0 {p : CuspParameters}
    (hp : p.BasicConditions) {x : Plane} (hx : ‖x‖ ≤ 4 * p.r₀) :
    p.atomicPerturbation x = 0 := by
  have hplus : p.cuspPlus x = 0 := by
    by_contra hn
    have hnorm := cuspPlus_tsupport_norm_lower p (subset_tsupport _ hn)
    linarith [hp.radius_large]
  have hminus : p.cuspMinus x = 0 := by
    by_contra hn
    have hnorm := cuspMinus_tsupport_norm_lower p (subset_tsupport _ hn)
    linarith [hp.radius_large]
  simp only [atomicPerturbation_eq_cusps, hplus, hminus, add_zero, mul_zero]

/-- The pointwise multiplier, integrated against any square-integrable state. -/
theorem mass_atomicPerturbation_mul_le_exterior {p : CuspParameters}
    (hp : p.BasicConditions) {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    mass (fun x => (p.atomicPerturbation x : ℂ) * φ x) ≤
      (2 * p.ε * p.a) ^ 2 * ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  let S : Set Plane := {x | 4 * p.r₀ ≤ ‖x‖}
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  have hmul := memLp_boundedPotential_mul p.atomicPerturbation (atomicPerturbation_continuous hp)
    (abs_atomicPerturbation_le_cusp_depth hp) hφ
  have hmajor : Integrable (fun x => (2 * p.ε * p.a) ^ 2 * ‖φ x‖ ^ 2) :=
    hφ.norm.integrable_sq.const_mul _
  calc
    mass (fun x => (p.atomicPerturbation x : ℂ) * φ x) ≤
        ∫ x : Plane, S.indicator (fun x => (2 * p.ε * p.a) ^ 2 * ‖φ x‖ ^ 2) x := by
      apply integral_mono hmul.norm.integrable_sq (hmajor.indicator hS)
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        change ‖(p.atomicPerturbation x : ℂ) * φ x‖ ^ 2 ≤
          (2 * p.ε * p.a) ^ 2 * ‖φ x‖ ^ 2
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hp.ε_pos.le) hp.a_pos.le)).mpr
          (abs_atomicPerturbation_le_cusp_depth hp x)
      · have hn : ‖x‖ ≤ 4 * p.r₀ := (lt_of_not_ge hx).le
        simp only [indicator_of_notMem hx, atomicPerturbation_zero_of_norm_le_four_r0 hp hn,
          Complex.ofReal_zero, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0), le_refl]
    _ = (2 * p.ε * p.a) ^ 2 * ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
      rw [integral_indicator hS, integral_const_mul]

/-- This uses the actual bounded L² multiplier and any of its representatives. -/
theorem norm_atomicPerturbationMul_sq_le_exterior {p : CuspParameters}
    (hp : p.BasicConditions) {u : L2Space} {φ : Wavefunction} (hu : Represents u φ) :
    ‖atomicPerturbationMul hp u‖ ^ 2 ≤
      (2 * p.ε * p.a) ^ 2 * ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  have hrep : Represents (atomicPerturbationMul hp u)
      (fun x => (p.atomicPerturbation x : ℂ) * φ x) := by
    filter_upwards [coe_atomicPerturbationMul hp u, hu] with x hx hux
    change (atomicPerturbationMul hp u) x = (p.atomicPerturbation x : ℂ) * φ x
    change (atomicPerturbationMul hp u) x = (p.atomicPerturbation x : ℂ) * u x at hx
    rw [hx, hux]
  rw [hrep.norm_sq_eq_mass]
  exact mass_atomicPerturbation_mul_le_exterior hp hu.memLp

/-- Quantitative exterior-mass bound for the actual core-to-full residual. -/
theorem norm_scaled_atomicPerturbationMul_sq_le_exterior {p : CuspParameters}
    (hp : p.BasicConditions) (coupling : ℝ)
    {u : L2Space} {φ : Wavefunction} (hu : Represents u φ) :
    ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ ^ 2 ≤
      (2 * coupling ^ 2 * p.ε * p.a) ^ 2 *
        ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  calc
    ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ ^ 2 =
        (coupling ^ 2) ^ 2 * ‖atomicPerturbationMul hp u‖ ^ 2 := by
      simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    _ ≤ (coupling ^ 2) ^ 2 * ((2 * p.ε * p.a) ^ 2 *
        ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_atomicPerturbationMul_sq_le_exterior hp hu) (sq_nonneg _)
    _ = (2 * coupling ^ 2 * p.ε * p.a) ^ 2 *
        ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by ring

end InfiniteZero.CuspParameters
