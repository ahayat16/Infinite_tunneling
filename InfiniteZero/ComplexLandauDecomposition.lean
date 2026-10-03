import InfiniteZero.ComplexLandauLocalProfile
import InfiniteZero.ComplexLandauTails

/-!
# Exact local and tail decomposition for the complex Landau kernel

The local profile uses the affine change of variables
`τ = bridgeTime b E r + sqrt h * u`. Splitting the positive proper-time axis
then identifies its integral with the normalized complex kernel minus its
actual tail integral. These are exact identities, without asymptotic inputs.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- Exact change of scale in the local proper-time integral. -/
theorem integral_complexLandauLocalProfile_eq {b E r ε h : ℝ} (δ : ℂ)
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hh : 0 < h) :
    (∫ u : ℝ, complexLandauLocalProfile b E r ε h δ u) =
      ((Real.sqrt h)⁻¹ : ℂ) *
        Complex.exp (((bridgeAction b E r : ℂ) +
          ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
        ∫ τ in Ioo (bridgeTime b E r - ε) (bridgeTime b E r + ε),
          complexLandauIntegrand b h E ((r : ℂ) + δ) τ := by
  let a := bridgeTime b E r
  let N := Complex.exp (((bridgeAction b E r : ℂ) +
    ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ))
  let g : ℝ → ℂ := (Ioo (a - ε) (a + ε)).indicator
    (fun τ => N * complexLandauIntegrand b h E ((r : ℂ) + δ) τ)
  have heq : complexLandauLocalProfile b E r ε h δ =
      fun u => g (a + Real.sqrt h * u) := by
    funext u
    exact complexLandauLocalProfile_eq_normalized hb hE hr ε h δ u
  rw [heq, Measure.integral_comp_mul_left (fun x => g (a + x)),
    integral_add_left_eq_self, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hh))]
  dsimp only [g]
  rw [integral_indicator measurableSet_Ioo, integral_const_mul]
  simp only [Complex.real_smul, mul_assoc, a, N, Complex.ofReal_inv]

/-- The exact positive-axis partition, including the boundary points in the tail. -/
theorem complexLandauIntegrand_integral_split {b h E r ε : ℝ} {δ : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E)
    (hQ : 0 < (((r : ℂ) + δ) ^ 2).re) (hεa : ε < bridgeTime b E r) :
    (∫ τ in Ioi (0 : ℝ), complexLandauIntegrand b h E ((r : ℂ) + δ) τ) =
      (∫ τ in Ioo (bridgeTime b E r - ε) (bridgeTime b E r + ε),
        complexLandauIntegrand b h E ((r : ℂ) + δ) τ) +
      ∫ τ in landauTailSet b E r ε, complexLandauIntegrand b h E ((r : ℂ) + δ) τ := by
  let a := bridgeTime b E r
  have hsets : landauTailSet b E r ε = Ioi 0 \ Ioo (a - ε) (a + ε) := by
    ext τ
    simp only [landauTailSet, mem_setOf_eq, mem_diff, mem_Ioi, mem_Ioo, not_and_or,
      not_lt, le_abs]
    constructor
    · rintro ⟨hτ, hleft | hright⟩
      · exact ⟨hτ, Or.inr (by dsimp [a]; linarith)⟩
      · exact ⟨hτ, Or.inl (by dsimp [a]; linarith)⟩
    · rintro ⟨hτ, hleft | hright⟩
      · exact ⟨hτ, Or.inr (by dsimp [a] at hleft; linarith)⟩
      · exact ⟨hτ, Or.inl (by dsimp [a] at hright; linarith)⟩
  have hsub : Ioo (a - ε) (a + ε) ⊆ Ioi 0 :=
    fun τ hτ => (sub_pos.mpr hεa).trans hτ.1
  rw [hsets, setIntegral_diff measurableSet_Ioo
    (integrableOn_complexLandauIntegrand hb hh hE hQ) hsub]
  ring

/-- Exact normalized decomposition, with `h^(3/2)` written as `h * sqrt h`. -/
theorem normalized_complexLandauKernel_decomposition {b E r ε h : ℝ} {δ : ℂ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r)
    (hεa : ε < bridgeTime b E r) (hh : 0 < h)
    (hQ : 0 < (((r : ℂ) + δ) ^ 2).re) :
    ((h * Real.sqrt h : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b E r : ℂ) +
          ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
        complexLandauKernel b h E ((r : ℂ) + δ) =
      ((b / (4 * Real.pi) : ℝ) : ℂ) *
        (∫ u : ℝ, complexLandauLocalProfile b E r ε h δ u) +
      ((h * Real.sqrt h : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b E r : ℂ) +
          ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
        complexLandauTailKernel b h E r ε δ := by
  rw [integral_complexLandauLocalProfile_eq δ hb hE hr hh]
  unfold complexLandauKernel complexLandauTailKernel
  rw [complexLandauIntegrand_integral_split hb hh hE hQ hεa]
  have hs : (Real.sqrt h : ℂ) ^ 2 = (h : ℂ) := by
    exact_mod_cast Real.sq_sqrt hh.le
  have hsn : (Real.sqrt h : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hh).ne'
  push_cast
  rw [← hs]
  field_simp

/-- The same exact identity in the power convention of the semiclassical formula. -/
theorem h_three_halves_normalized_complexLandauKernel_decomposition {b E r ε h : ℝ}
    {δ : ℂ} (hb : 0 < b) (hE : 0 < E) (hr : 0 < r)
    (hεa : ε < bridgeTime b E r) (hh : 0 < h)
    (hQ : 0 < (((r : ℂ) + δ) ^ 2).re) :
    ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b E r : ℂ) +
          ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
        complexLandauKernel b h E ((r : ℂ) + δ) =
      ((b / (4 * Real.pi) : ℝ) : ℂ) *
        (∫ u : ℝ, complexLandauLocalProfile b E r ε h δ u) +
      ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b E r : ℂ) +
          ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
        complexLandauTailKernel b h E r ε δ := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hh, Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  exact normalized_complexLandauKernel_decomposition hb hE hr hεa hh hQ

end InfiniteZero
