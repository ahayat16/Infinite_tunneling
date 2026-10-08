import InfiniteZero.MagneticModel

/-!
# A weighted Cauchy–Schwarz bound for an integral-kernel row

The absolute mass of one kernel row controls its action on a source by
the corresponding weighted square integral. The proof integrates the
nonnegative weighted variance; it does not assume a pre-existing bounded
integral operator.
-/

noncomputable section

open MeasureTheory

namespace InfiniteZero

/-- A row of an integral kernel with absolute mass at most `M` satisfies
the weighted squared-norm bound used in Schur's test. -/
theorem integralKernel_row_bound {K : Plane → ℂ} {f : Wavefunction} {M : ℝ}
    (hK : Integrable K)
    (h1 : Integrable (fun y => ‖K y‖ * ‖f y‖))
    (h2 : Integrable (fun y => ‖K y‖ * ‖f y‖ ^ 2))
    (hM : 0 < M) (hmass : (∫ y : Plane, ‖K y‖) ≤ M) :
    ‖∫ y : Plane, K y * f y‖ ^ 2 ≤
      M * ∫ y : Plane, ‖K y‖ * ‖f y‖ ^ 2 := by
  let a : ℝ := ∫ y : Plane, ‖K y‖ * ‖f y‖
  let b : ℝ := ∫ y : Plane, ‖K y‖ * ‖f y‖ ^ 2
  let m : ℝ := ∫ y : Plane, ‖K y‖
  let c : ℝ := a / M
  have hc : c * M = a := div_mul_cancel₀ a hM.ne'
  have hvar : 0 ≤ b - 2 * c * a + c ^ 2 * m := by
    have hn : 0 ≤ ∫ y : Plane, ‖K y‖ * (‖f y‖ - c) ^ 2 :=
      integral_nonneg
        (fun y : Plane => mul_nonneg (norm_nonneg (K y)) (sq_nonneg (‖f y‖ - c)))
    have heq : (fun y : Plane => ‖K y‖ * (‖f y‖ - c) ^ 2) =
        (fun y => ‖K y‖ * ‖f y‖ ^ 2 - (2 * c) * (‖K y‖ * ‖f y‖) +
          c ^ 2 * ‖K y‖) := by
      funext y
      ring
    have hsub : Integrable (fun y : Plane =>
        ‖K y‖ * ‖f y‖ ^ 2 - (2 * c) * (‖K y‖ * ‖f y‖)) :=
      h2.sub (h1.const_mul (2 * c))
    rw [heq, integral_add hsub
        (hK.norm.const_mul (c ^ 2)),
      integral_sub h2 (h1.const_mul (2 * c)), integral_const_mul,
      integral_const_mul] at hn
    exact hn
  have hvarM : 0 ≤ b - 2 * c * a + c ^ 2 * M := by
    have hm : c ^ 2 * m ≤ c ^ 2 * M :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg c)
    linarith
  have hsquare : a ^ 2 ≤ M * b := by
    have hp := mul_nonneg hM.le hvarM
    have heq : M * (b - 2 * c * a + c ^ 2 * M) = M * b - a ^ 2 := by
      calc
        _ = M * b - 2 * (c * M) * a + (c * M) ^ 2 := by ring
        _ = _ := by rw [hc]; ring
    rw [heq] at hp
    linarith
  have hnorm : ‖∫ y : Plane, K y * f y‖ ≤ a := by
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun y : Plane => K y * f y)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsquare

end InfiniteZero
