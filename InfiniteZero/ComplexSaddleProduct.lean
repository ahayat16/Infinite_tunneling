import InfiniteZero.ComplexSaddleAbsolute
import Mathlib.MeasureTheory.Integral.Prod

/-! Absolute estimates on the actual product saddle contour. The restriction
can be chosen to keep both normal coordinates in the local analytic window.
No physical amplitude bound is assumed to have been proved here. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

def logFlatSaddleContourIntegrand (β k tStar : ℝ) (c : ℂ) (h q : ℝ) : ℂ :=
  Complex.exp (-logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
    (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h) + (q : ℂ)))

def logFlatSaddleProductIntegrand (β k tStar : ℝ) (c d : ℂ) (h : ℝ)
    (q : ℝ × ℝ) : ℂ :=
  logFlatSaddleContourIntegrand β k tStar c h q.1 *
    logFlatSaddleContourIntegrand β k tStar d h q.2

theorem eventually_integrable_logFlatSaddleProduct {β k tStar : ℝ} {c d : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (logFlatSaddleProductIntegrand β k tStar c d h)
      ((volume : Measure ℝ).prod volume) := by
  filter_upwards [eventually_integrable_logFlatSaddleHorizontal (k := k) hβ ht hc,
    eventually_integrable_logFlatSaddleHorizontal (k := k) hβ ht hd] with h hic hid
  exact hic.mul_prod hid

theorem integral_norm_logFlatSaddleProduct (β k tStar : ℝ) (c d : ℂ) (h : ℝ) :
    (∫ q, ‖logFlatSaddleProductIntegrand β k tStar c d h q‖
      ∂(volume : Measure ℝ).prod volume) =
    (∫ x, ‖logFlatSaddleContourIntegrand β k tStar c h x‖) *
      (∫ y, ‖logFlatSaddleContourIntegrand β k tStar d h y‖) := by
  simp only [logFlatSaddleProductIntegrand, norm_mul]
  exact integral_prod_mul
    (fun x : ℝ => ‖logFlatSaddleContourIntegrand β k tStar c h x‖)
    (fun y : ℝ => ‖logFlatSaddleContourIntegrand β k tStar d h y‖)

theorem eventually_logFlatSaddleProduct_absolute_bound {β k tStar : ℝ} {c d : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖logFlatSaddleNormalizer β k tStar c h * logFlatSaddleNormalizer β k tStar d h‖ *
        (∫ q, ‖logFlatSaddleProductIntegrand β k tStar c d h q‖
          ∂(volume : Measure ℝ).prod volume) ≤ horizontalSaddleAbsoluteConstant β ^ 2 := by
  filter_upwards [eventually_logFlatSaddle_absolute_bound (k := k) hβ ht hc,
    eventually_logFlatSaddle_absolute_bound (k := k) hβ ht hd] with h hbc hbd
  change ‖logFlatSaddleNormalizer β k tStar c h‖ *
    (∫ q, ‖logFlatSaddleContourIntegrand β k tStar c h q‖) ≤ _ at hbc
  change ‖logFlatSaddleNormalizer β k tStar d h‖ *
    (∫ q, ‖logFlatSaddleContourIntegrand β k tStar d h q‖) ≤ _ at hbd
  rw [norm_mul, integral_norm_logFlatSaddleProduct]
  calc
    _ = (‖logFlatSaddleNormalizer β k tStar c h‖ *
        (∫ q, ‖logFlatSaddleContourIntegrand β k tStar c h q‖)) *
      (‖logFlatSaddleNormalizer β k tStar d h‖ *
        (∫ q, ‖logFlatSaddleContourIntegrand β k tStar d h q‖)) := by ring
    _ ≤ _ := by
      simpa only [pow_two] using mul_le_mul hbc hbd
        (mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _)))
        (horizontalSaddleAbsoluteConstant_pos β).le

/-- The bound survives any restriction, including the product of the two
truncated saddle rays. The threshold is independent of the restricting set. -/
theorem eventually_forall_logFlatSaddleProduct_restrict_bound
    {β k tStar : ℝ} {c d : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ S : Set (ℝ × ℝ),
      ‖logFlatSaddleNormalizer β k tStar c h * logFlatSaddleNormalizer β k tStar d h‖ *
        (∫ q in S, ‖logFlatSaddleProductIntegrand β k tStar c d h q‖
          ∂(volume : Measure ℝ).prod volume) ≤ horizontalSaddleAbsoluteConstant β ^ 2 := by
  filter_upwards [eventually_integrable_logFlatSaddleProduct (k := k) hβ ht hc hd,
    eventually_logFlatSaddleProduct_absolute_bound (k := k) hβ ht hc hd] with h hi hb
  intro S
  exact (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hi.norm (Eventually.of_forall fun _ => norm_nonneg _))
    (norm_nonneg _)).trans hb

/-- A multiplier close to a constant on the local product contour produces
an error bounded by the same smallness times a constant depending only on β.
Integrability and the physical multiplier estimate remain explicit inputs. -/
theorem eventually_logFlatSaddleProduct_multiplier_bound
    {β k tStar : ℝ} {c d : ℂ} (hβ : 0 < β) (ht : 0 < tStar)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ (S : Set (ℝ × ℝ)) (B : ℝ × ℝ → ℂ)
      (B₀ : ℂ) (ε : ℝ), 0 ≤ ε →
      IntegrableOn (fun q => logFlatSaddleProductIntegrand β k tStar c d h q * B q) S
        ((volume : Measure ℝ).prod volume) →
      (∀ᵐ q ∂((volume : Measure ℝ).prod volume).restrict S, ‖B q - B₀‖ ≤ ε) →
      ‖(logFlatSaddleNormalizer β k tStar c h * logFlatSaddleNormalizer β k tStar d h) *
        ((∫ q in S, logFlatSaddleProductIntegrand β k tStar c d h q * B q
            ∂(volume : Measure ℝ).prod volume) -
          B₀ * ∫ q in S, logFlatSaddleProductIntegrand β k tStar c d h q
            ∂(volume : Measure ℝ).prod volume)‖ ≤ horizontalSaddleAbsoluteConstant β ^ 2 * ε := by
  filter_upwards [eventually_integrable_logFlatSaddleProduct (k := k) hβ ht hc hd,
    eventually_forall_logFlatSaddleProduct_restrict_bound (k := k) hβ ht hc hd] with h hi hb
  intro S B B₀ ε hε hB he
  exact norm_normalized_integral_sub_le_of_bound hi.integrableOn hB hε he (hb S)

end InfiniteZero
