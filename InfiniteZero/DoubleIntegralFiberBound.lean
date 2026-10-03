import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bounds for a double integral from bounds on its fibers

These Fubini estimates apply directly to restricted measures, for example to
products of two rays. Joint integrability justifies the passage to iterated
integrals. The real majorant is integrable; its domination of a norm already
implies the nonnegativity needed for the estimate.
-/

noncomputable section

open MeasureTheory Filter

namespace InfiniteZero

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- Integrate a bound for fibers in the first variable. -/
theorem norm_integral_prod_le_of_fiber_bound
    {F : α × β → E} (hF : Integrable F (μ.prod ν))
    {g : β → ℝ} (hg : Integrable g ν) {D : ℝ}
    (hbound : ∀ᵐ y ∂ν, ‖∫ x, F (x, y) ∂μ‖ ≤ D * g y) :
    ‖∫ z, F z ∂μ.prod ν‖ ≤ D * ∫ y, g y ∂ν := by
  rw [integral_prod_symm F hF, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hg.const_mul D) hbound

/-- Integrate a bound for fibers in the second variable. -/
theorem norm_integral_prod_le_of_fiber_bound_left
    {F : α × β → E} (hF : Integrable F (μ.prod ν))
    {g : α → ℝ} (hg : Integrable g μ) {D : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖∫ y, F (x, y) ∂ν‖ ≤ D * g x) :
    ‖∫ z, F z ∂μ.prod ν‖ ≤ D * ∫ x, g x ∂μ := by
  rw [integral_prod F hF, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hg.const_mul D) hbound

/-- A bound on the integral of a difference on almost every first-variable
fiber bounds the difference of the two product integrals. -/
theorem norm_integral_prod_sub_le_of_fiber_bound
    {F G : α × β → E} (hF : Integrable F (μ.prod ν))
    (hG : Integrable G (μ.prod ν))
    {g : β → ℝ} (hg : Integrable g ν) {D : ℝ}
    (hbound : ∀ᵐ y ∂ν, ‖∫ x, (F (x, y) - G (x, y)) ∂μ‖ ≤ D * g y) :
    ‖(∫ z, F z ∂μ.prod ν) - ∫ z, G z ∂μ.prod ν‖ ≤
      D * ∫ y, g y ∂ν := by
  rw [← integral_sub hF hG]
  exact norm_integral_prod_le_of_fiber_bound (hF.sub hG) hg hbound

/-- The second-variable version of the difference estimate. -/
theorem norm_integral_prod_sub_le_of_fiber_bound_left
    {F G : α × β → E} (hF : Integrable F (μ.prod ν))
    (hG : Integrable G (μ.prod ν))
    {g : α → ℝ} (hg : Integrable g μ) {D : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖∫ y, (F (x, y) - G (x, y)) ∂ν‖ ≤ D * g x) :
    ‖(∫ z, F z ∂μ.prod ν) - ∫ z, G z ∂μ.prod ν‖ ≤
      D * ∫ x, g x ∂μ := by
  rw [← integral_sub hF hG]
  exact norm_integral_prod_le_of_fiber_bound_left (hF.sub hG) hg hbound

/-- The hypothesis can instead be a difference of first-variable fiber
integrals. Their almost-everywhere integrability follows from `hF` and `hG`. -/
theorem norm_integral_prod_sub_le_of_fiber_integral_sub_bound
    {F G : α × β → E} (hF : Integrable F (μ.prod ν))
    (hG : Integrable G (μ.prod ν))
    {g : β → ℝ} (hg : Integrable g ν) {D : ℝ}
    (hbound : ∀ᵐ y ∂ν,
      ‖(∫ x, F (x, y) ∂μ) - ∫ x, G (x, y) ∂μ‖ ≤ D * g y) :
    ‖(∫ z, F z ∂μ.prod ν) - ∫ z, G z ∂μ.prod ν‖ ≤
      D * ∫ y, g y ∂ν := by
  apply norm_integral_prod_sub_le_of_fiber_bound hF hG hg
  filter_upwards [hbound, hF.prod_left_ae, hG.prod_left_ae] with y hy hFy hGy
  rwa [integral_sub hFy hGy]

/-- The version using differences of second-variable fiber integrals. -/
theorem norm_integral_prod_sub_le_of_fiber_integral_sub_bound_left
    {F G : α × β → E} (hF : Integrable F (μ.prod ν))
    (hG : Integrable G (μ.prod ν))
    {g : α → ℝ} (hg : Integrable g μ) {D : ℝ}
    (hbound : ∀ᵐ x ∂μ,
      ‖(∫ y, F (x, y) ∂ν) - ∫ y, G (x, y) ∂ν‖ ≤ D * g x) :
    ‖(∫ z, F z ∂μ.prod ν) - ∫ z, G z ∂μ.prod ν‖ ≤
      D * ∫ x, g x ∂μ := by
  apply norm_integral_prod_sub_le_of_fiber_bound_left hF hG hg
  filter_upwards [hbound, hF.prod_right_ae, hG.prod_right_ae] with x hx hFx hGx
  rwa [integral_sub hFx hGx]

end InfiniteZero
