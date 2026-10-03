import InfiniteZero.ComplexSaddleBranches
import InfiniteZero.ComplexSaddleLeading

/-!
# Leading asymptotic on the actual log-flat saddle line

The full horizontal line is centered at the constructed critical point.
Identifying this integral with the original cutoff integral requires the
separate contour and truncation estimates; no such identification is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

theorem integral_logFlatComplexPhase_saddle {β k : ℝ} (hβ : β ≠ 0) {C w : ℂ}
    (hc : C * Complex.exp (-logFlatComplexCritical β k w) = 2 * (β : ℂ) * w) :
    (∫ q : ℝ, Complex.exp (-logFlatComplexPhase β k C
      (logFlatComplexCritical β k w + (q : ℂ)))) =
      Complex.exp (-logFlatComplexPhase β k C (logFlatComplexCritical β k w)) *
        horizontalSaddleIntegral β w := by
  have he (q : ℝ) : logFlatComplexPhase β k C (logFlatComplexCritical β k w + (q : ℂ)) =
      logFlatComplexPhase β k C (logFlatComplexCritical β k w) + horizontalSaddlePhase β w q := by
    have hd := logFlatComplexPhase_difference hβ hc (q : ℂ)
    have hp : (β : ℂ) * (q : ℂ) ^ 2 + 2 * (β : ℂ) * w *
        (Complex.exp (-(q : ℂ)) - 1 + (q : ℂ)) = horizontalSaddlePhase β w q := by
      simp [horizontalSaddlePhase, exponentialRemainder, Complex.ofReal_exp]
    rw [hp] at hd
    linear_combination hd
  simp_rw [he, neg_add, Complex.exp_add]
  exact integral_const_mul _ _

def logFlatSaddleHorizontalIntegral (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℂ :=
  ∫ q : ℝ, Complex.exp (-logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
    (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h) + (q : ℂ)))

theorem tendsto_logFlatSaddle_horizontal_leading {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    Tendsto (fun h : ℝ => (Real.sqrt (logFlatSaddleRoot β k tStar c h).re : ℂ) *
      Complex.exp (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))) *
      logFlatSaddleHorizontalIntegral β k tStar c h) (𝓝[>] 0)
        (𝓝 ((Real.sqrt (Real.pi / β) : ℝ) : ℂ)) := by
  have him : ∀ᶠ h : ℝ in 𝓝[>] 0,
      |(logFlatSaddleRoot β k tStar c h).im| ≤
        ‖logFlatLambertDisplacement β k tStar c‖ + Real.pi := by
    filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc] with h hs
    exact hs.2.2.2
  have hlim := tendsto_sqrt_re_mul_horizontalSaddleIntegral hβ
    (tendsto_re_logFlatSaddleRoot (k := k) hβ.ne' ht.ne' hc) him
  apply hlim.congr'
  filter_upwards [eventually_logFlatSaddleRoot_critical (k := k) hβ.ne' ht.ne' hc] with h hs
  rw [logFlatSaddleHorizontalIntegral, integral_logFlatComplexPhase_saddle hβ.ne' hs.1]
  simp [Complex.exp_neg, mul_assoc]

theorem eventually_logFlatSaddle_horizontal_ne_zero {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, logFlatSaddleHorizontalIntegral β k tStar c h ≠ 0 := by
  have hnonzero : ((Real.sqrt (Real.pi / β) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hβ)).ne'
  filter_upwards [(tendsto_logFlatSaddle_horizontal_leading (k := k) hβ ht hc).eventually_ne hnonzero]
    with h hh
  intro he
  exact hh (by rw [he, mul_zero])

end InfiniteZero
