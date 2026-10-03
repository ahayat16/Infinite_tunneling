import InfiniteZero.AtomicWeightedTail
import InfiniteZero.BoundedMultiplierLimits
import InfiniteZero.AtomicPerturbationSign

/-!
# Operations on the actual exponential weight multipliers

The bounded real multiplier `exp (κ λ T)` is self-adjoint and has the explicit
bounded inverse `exp (-κ λ T)`. For nonnegative parameters and weight, it
expands the L² norm, while its inverse is a contraction. These statements
concern the concrete L² multipliers and impose no differential-domain claim.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

variable (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
  (hT : ∀ x, T x ∈ Icc 0 M)

theorem isSelfAdjoint_atomicExponentialWeightMul (coupling κ : ℝ) :
    IsSelfAdjoint (atomicExponentialWeightMul T hTc hT coupling κ) :=
  isSelfAdjoint_boundedPotentialMul _ _ _

/-- A nonnegative exponential weight expands the physical L² norm. -/
theorem norm_le_atomicExponentialWeightMul {coupling κ : ℝ}
    (hc : 0 ≤ coupling) (hκ : 0 ≤ κ) (u : L2Space) :
    ‖u‖ ≤ ‖atomicExponentialWeightMul T hTc hT coupling κ u‖ := by
  apply norm_lower_boundedPotentialMul
  intro x
  exact Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg hκ hc) (hT x).1)

/-- Multiplication by the negative exponential is an exact right inverse. -/
theorem atomicExponentialWeightMul_neg_cancel (coupling κ : ℝ) (u : L2Space) :
    atomicExponentialWeightMul T hTc hT coupling κ
      (atomicExponentialWeightMul T hTc hT coupling (-κ) u) = u := by
  apply Lp.ext
  filter_upwards [coe_atomicExponentialWeightMul T hTc hT coupling κ
    (atomicExponentialWeightMul T hTc hT coupling (-κ) u),
    coe_atomicExponentialWeightMul T hTc hT coupling (-κ) u] with x hout hin
  rw [hout, hin, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  have he : κ * coupling * T x + -κ * coupling * T x = 0 := by ring
  rw [he, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- Multiplication by the negative exponential is also an exact left inverse. -/
theorem atomicExponentialWeightMul_neg_cancel_left (coupling κ : ℝ) (u : L2Space) :
    atomicExponentialWeightMul T hTc hT coupling (-κ)
      (atomicExponentialWeightMul T hTc hT coupling κ u) = u := by
  simpa only [neg_neg] using atomicExponentialWeightMul_neg_cancel T hTc hT coupling (-κ) u

theorem atomicExponentialWeightMul_comp_neg (coupling κ : ℝ) :
    (atomicExponentialWeightMul T hTc hT coupling κ).comp
      (atomicExponentialWeightMul T hTc hT coupling (-κ)) =
        ContinuousLinearMap.id ℂ L2Space := by
  apply ContinuousLinearMap.ext
  intro u
  exact atomicExponentialWeightMul_neg_cancel T hTc hT coupling κ u

theorem atomicExponentialWeightMul_neg_comp (coupling κ : ℝ) :
    (atomicExponentialWeightMul T hTc hT coupling (-κ)).comp
      (atomicExponentialWeightMul T hTc hT coupling κ) =
        ContinuousLinearMap.id ℂ L2Space := by
  apply ContinuousLinearMap.ext
  intro u
  exact atomicExponentialWeightMul_neg_cancel_left T hTc hT coupling κ u

/-- The explicit inverse is contractive for nonnegative weight parameters. -/
theorem norm_atomicExponentialWeightMul_neg_le {coupling κ : ℝ}
    (hc : 0 ≤ coupling) (hκ : 0 ≤ κ) (u : L2Space) :
    ‖atomicExponentialWeightMul T hTc hT coupling (-κ) u‖ ≤ ‖u‖ := by
  have h := norm_le_atomicExponentialWeightMul T hTc hT hc hκ
    (atomicExponentialWeightMul T hTc hT coupling (-κ) u)
  rwa [atomicExponentialWeightMul_neg_cancel T hTc hT coupling κ u] at h

/-- Exact identity for the defect multiplier, on every L² vector. -/
theorem atomicExponentialWeightDefectMul_apply_eq_sub (coupling κ : ℝ) (u : L2Space) :
    atomicExponentialWeightDefectMul T hTc hT coupling κ u =
      atomicExponentialWeightMul T hTc hT coupling κ u - u := by
  rw [atomicExponentialWeightMul_apply_eq_add, add_sub_cancel_left]

/-- At zero strength the actual multiplier is the identity operator. -/
theorem atomicExponentialWeightMul_zero (coupling : ℝ) :
    atomicExponentialWeightMul T hTc hT coupling 0 =
      ContinuousLinearMap.id ℂ L2Space := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [coe_atomicExponentialWeightMul T hTc hT coupling 0 u] with x hx
  simpa only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using hx

end InfiniteZero
