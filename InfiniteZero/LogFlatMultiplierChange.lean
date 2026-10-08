import InfiniteZero.ComplexLogFlatChange

/-!
# Exact logarithmic changes with a variable multiplier

These are Lebesgue changes of variables, including the Jacobians. The
multiplier may depend jointly on the two normal coordinates. No
factorization or analytic extension of that multiplier is assumed.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

theorem integral_complexLogFlat_multiplier_logarithmic_change
    {tStar t₂ : ℝ} (ht : 0 < tStar) (ht₂ : 0 < t₂)
    (β h : ℝ) (c : ℂ) (m : ℕ) (B : ℝ → ℂ) :
    (∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t * B t) =
      (tStar : ℂ) ^ (m + 1) *
        ∫ y in Ioi (Real.log (tStar / t₂)),
          Complex.exp (-logFlatComplexPhase β (m : ℝ)
            (c * (tStar : ℂ) / (h : ℂ)) (y : ℂ)) * B (tStar * Real.exp (-y)) := by
  rw [integral_logarithmic_substitution ht ht₂, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  have hj := complexLogFlatIntegrand_logarithmic_chart ht β h c m y
  change ((tStar * Real.exp (-y) : ℝ) : ℂ) *
    complexLogFlatIntegrand β tStar h c m (tStar * Real.exp (-y)) = _ at hj
  change ((tStar * Real.exp (-y) : ℝ) : ℂ) *
    (complexLogFlatIntegrand β tStar h c m (tStar * Real.exp (-y)) *
      B (tStar * Real.exp (-y))) = _
  rw [← mul_assoc, hj, mul_assoc]

/-- Each substitution contributes `tStar^(m+1)`. For the physical moment
`m=2`, their product is exactly `tStar^6`, including both Jacobians. -/
theorem integral_complexLogFlat_product_multiplier_logarithmic_change
    {tStar t₂ : ℝ} (ht : 0 < tStar) (ht₂ : 0 < t₂)
    (β h : ℝ) (c : ℂ) (m : ℕ) (B : ℝ → ℝ → ℂ) :
    (∫ t in Ioo 0 t₂, ∫ u in Ioo 0 t₂,
      complexLogFlatIntegrand β tStar h c m t *
        complexLogFlatIntegrand β tStar h c m u * B t u) =
      (tStar : ℂ) ^ (2 * (m + 1)) *
        ∫ x in Ioi (Real.log (tStar / t₂)), ∫ y in Ioi (Real.log (tStar / t₂)),
          Complex.exp (-logFlatComplexPhase β (m : ℝ)
            (c * (tStar : ℂ) / (h : ℂ)) (x : ℂ)) *
          Complex.exp (-logFlatComplexPhase β (m : ℝ)
            (c * (tStar : ℂ) / (h : ℂ)) (y : ℂ)) *
          B (tStar * Real.exp (-x)) (tStar * Real.exp (-y)) := by
  let f := complexLogFlatIntegrand β tStar h c m
  let g : ℝ → ℂ := fun y => Complex.exp (-logFlatComplexPhase β (m : ℝ)
    (c * (tStar : ℂ) / (h : ℂ)) (y : ℂ))
  let P : ℂ := (tStar : ℂ) ^ (m + 1)
  let S := Ioi (Real.log (tStar / t₂))
  have hinner (t : ℝ) :
      (∫ u in Ioo 0 t₂, f t * f u * B t u) =
        P * (f t * ∫ y in S, g y * B t (tStar * Real.exp (-y))) := by
    simp_rw [mul_assoc (f t)]
    rw [integral_const_mul, integral_complexLogFlat_multiplier_logarithmic_change ht ht₂]
    dsimp only [P, g, S]
    ring
  change (∫ t in Ioo 0 t₂, ∫ u in Ioo 0 t₂, f t * f u * B t u) = _
  simp_rw [hinner]
  rw [integral_const_mul, integral_complexLogFlat_multiplier_logarithmic_change ht ht₂]
  have hp : P * P = (tStar : ℂ) ^ (2 * (m + 1)) := by
    dsimp [P]
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = (P * P) * ∫ x in S, ∫ y in S,
        g x * g y * B (tStar * Real.exp (-x)) (tStar * Real.exp (-y)) := by
      simp_rw [mul_assoc (g _), integral_const_mul]
      dsimp only [P, g, S]
      ring
    _ = _ := by rw [hp]

end InfiniteZero
