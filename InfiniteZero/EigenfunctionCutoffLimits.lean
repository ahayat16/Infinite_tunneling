import InfiniteZero.MagneticModel
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limits of bounded real cutoffs against an L² state

The dominating function is a constant times the squared norm of the state.
No differential energy, compact support, or measurability assumption on the
pointwise limit is needed. These statements do not assert weighted decay.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace InfiniteZero

/-- Bounded measurable real multipliers converge under the probability-density
integral. The common bound is independent of the sequence index. -/
theorem tendsto_integral_mul_sq_norm_of_bounded {φ : Wavefunction}
    (hφ : MemLp φ 2 volume) {a : ℕ → Plane → ℝ} {aLimit : Plane → ℝ} {C : ℝ}
    (ha : ∀ n, Measurable (a n)) (hbound : ∀ n x, |a n x| ≤ C)
    (hlim : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 (aLimit x))) :
    Tendsto (fun n => ∫ x : Plane, a n x * ‖φ x‖ ^ 2) atTop
      (𝓝 (∫ x : Plane, aLimit x * ‖φ x‖ ^ 2)) := by
  have hmass : Integrable (fun x => ‖φ x‖ ^ 2) :=
    hφ.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖φ x‖ ^ 2)
  · intro n
    exact (ha n).aestronglyMeasurable.mul (hφ.aestronglyMeasurable.norm.pow 2)
  · exact hmass.const_mul C
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_mul, abs_sq] using
        mul_le_mul_of_nonneg_right (hbound n x) (sq_nonneg ‖φ x‖)
  · exact Filter.Eventually.of_forall fun x => (hlim x).mul_const (‖φ x‖ ^ 2)

/-- Multiplying an L² state by bounded real cutoffs preserves mass in the
pointwise limit. The limit cutoff need not be supplied as measurable. -/
theorem tendsto_mass_real_cutoff_of_bounded {φ : Wavefunction}
    (hφ : MemLp φ 2 volume) {c : ℕ → Plane → ℝ} {cLimit : Plane → ℝ} {C : ℝ}
    (hc : ∀ n, Measurable (c n)) (hbound : ∀ n x, |c n x| ≤ C)
    (hlim : ∀ x, Tendsto (fun n => c n x) atTop (𝓝 (cLimit x))) :
    Tendsto (fun n => mass (fun x => (c n x : ℂ) * φ x)) atTop
      (𝓝 (mass (fun x => (cLimit x : ℂ) * φ x))) := by
  have hs : ∀ n x, |c n x ^ 2| ≤ C ^ 2 := by
    intro n x
    rw [abs_sq]
    exact sq_le_sq' (abs_le.mp (hbound n x)).1 (abs_le.mp (hbound n x)).2
  have h := tendsto_integral_mul_sq_norm_of_bounded hφ
    (fun n => (hc n).pow_const 2) hs (fun x => (hlim x).pow 2)
  simpa only [mass, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end InfiniteZero
