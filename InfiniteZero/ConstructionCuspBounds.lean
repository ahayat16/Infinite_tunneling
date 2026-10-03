import InfiniteZero.ConstructionSupportSeparation
import InfiniteZero.BridgeAction

/-!
# Quantitative outgoing geometry on the closed cusp supports

The elementary width condition gives the explicit constants `cₓ = cᵣ = 1/4`
in the one-sided horizontal and radial inequalities of L2.9. All conclusions
hold on the topological supports, including the tips and chart boundaries.
-/

noncomputable section

open Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- The exact squared-radius identity in the orthonormal cusp coordinates. -/
theorem norm_sq_cusp_coordinates (p : CuspParameters) (x : Plane) :
    ‖x‖ ^ 2 = p.R ^ 2 + p.R * p.normalCoordinate x -
      Real.sqrt 3 * p.R * p.tangentCoordinate x +
      p.normalCoordinate x ^ 2 + p.tangentCoordinate x ^ 2 := by
  have hx₀ := congrArg (fun y : Plane => y 0) (cuspFrame_reconstruction p x)
  have hx₁ := congrArg (fun y : Plane => y 1) (cuspFrame_reconstruction p x)
  simp [cuspTip, cuspNormal, cuspTangent] at hx₀ hx₁
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, hx₀, hx₁]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem cuspPlus_support_normal_bounds (p : CuspParameters) {x : Plane}
    (hx : x ∈ Function.support p.cuspPlus) :
    0 < p.normalCoordinate x ∧ p.normalCoordinate x < p.t₀ := by
  have hc : 0 < p.normalCoordinate x ∧ p.normalCoordinate x < p.t₀ ∧
      |p.tangentCoordinate x / p.normalCoordinate x ^ 2| < p.s₀ := by
    by_contra hn
    exact hx (by simp [cuspPlus, hn])
  exact ⟨hc.1, hc.2.1⟩

theorem cuspPlus_tsupport_normal_le (p : CuspParameters) :
    tsupport p.cuspPlus ⊆ {x | p.normalCoordinate x ≤ p.t₀} := by
  exact closure_minimal (fun _ hx => (cuspPlus_support_normal_bounds p hx).2.le)
    (isClosed_le (normalCoordinate_contDiff p).continuous continuous_const)

/-- The tangential perturbation can consume at most half the normal gain. -/
theorem cusp_tangential_correction_bound {p : CuspParameters} (h : p.BasicConditions)
    {t u : ℝ} (ht : 0 ≤ t) (htt₀ : t ≤ p.t₀) (hu : |u| ≤ p.s₀ * t ^ 2) :
    |Real.sqrt 3 * u| ≤ t / 2 := by
  have hs : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hw : Real.sqrt 3 * p.s₀ * t ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left htt₀ (mul_nonneg hs h.s₀_pos.le)).trans h.width_small
  have h₁ := mul_le_mul_of_nonneg_left hu hs
  have h₂ := mul_le_mul_of_nonneg_right hw ht
  rw [abs_mul, abs_of_nonneg hs]
  nlinarith

/-- Explicit one-sided bounds for every point in the closed quadratic chart. -/
theorem cusp_horizontal_radial_bounds {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (ht : 0 ≤ p.normalCoordinate x) (htt₀ : p.normalCoordinate x ≤ p.t₀)
    (hu : |p.tangentCoordinate x| ≤ p.s₀ * p.normalCoordinate x ^ 2) :
    x 0 ≤ p.R / 2 - p.normalCoordinate x / 4 ∧
      p.R + p.normalCoordinate x / 4 ≤ ‖x‖ := by
  have hcorr := cusp_tangential_correction_bound h ht htt₀ hu
  have hlo := neg_le_of_abs_le hcorr
  have hhi := le_of_abs_le hcorr
  have hx₀ := congrArg (fun y : Plane => y 0) (cuspFrame_reconstruction p x)
  simp [cuspTip, cuspNormal, cuspTangent] at hx₀
  refine ⟨by linarith, ?_⟩
  have hRs := mul_le_mul_of_nonneg_left hhi h.radius_pos.le
  have hsquare : (p.R + p.normalCoordinate x / 4) ^ 2 ≤ ‖x‖ ^ 2 := by
    apply sub_nonneg.mp
    have heq : ‖x‖ ^ 2 - (p.R + p.normalCoordinate x / 4) ^ 2 =
        (p.R * (p.normalCoordinate x / 2) - p.R * (Real.sqrt 3 * p.tangentCoordinate x)) +
        (15 / 16 : ℝ) * p.normalCoordinate x ^ 2 + p.tangentCoordinate x ^ 2 := by
      rw [norm_sq_cusp_coordinates]
      ring
    rw [heq]
    exact add_nonneg (add_nonneg (sub_nonneg.mpr hRs) (by positivity)) (sq_nonneg _)
  exact (sq_le_sq₀ (add_nonneg h.radius_pos.le (div_nonneg ht (by norm_num)))
    (norm_nonneg x)).mp hsquare

theorem cuspPlus_tsupport_horizontal_radial {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    x 0 ≤ p.R / 2 - p.normalCoordinate x / 4 ∧
      p.R + p.normalCoordinate x / 4 ≤ ‖x‖ := by
  have hc := cuspPlus_tsupport_subset_quadratic p hx
  exact cusp_horizontal_radial_bounds h hc.1 (cuspPlus_tsupport_normal_le p hx) hc.2

theorem cuspPlus_tsupport_horizontal {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    x 0 ≤ p.R / 2 - p.normalCoordinate x / 4 :=
  (cuspPlus_tsupport_horizontal_radial h hx).1

theorem cuspPlus_tsupport_radial {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    p.R + p.normalCoordinate x / 4 ≤ ‖x‖ :=
  (cuspPlus_tsupport_horizontal_radial h hx).2

theorem cuspPlus_support_horizontal {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ Function.support p.cuspPlus) :
    x 0 ≤ p.R / 2 - p.normalCoordinate x / 4 :=
  cuspPlus_tsupport_horizontal h (subset_tsupport p.cuspPlus hx)

theorem cuspPlus_support_radial {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ Function.support p.cuspPlus) :
    p.R + p.normalCoordinate x / 4 ≤ ‖x‖ :=
  cuspPlus_tsupport_radial h (subset_tsupport p.cuspPlus hx)

/-- The three geometric inequalities of L2.9, on the closed upper support. -/
theorem cuspPlus_tsupport_outgoing_bounds {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    x 0 ≤ p.R / 2 - p.normalCoordinate x / 4 ∧
      p.R + p.normalCoordinate x / 4 ≤ ‖x‖ ∧ Real.sqrt 3 * p.R / 2 ≤ x 1 :=
  ⟨cuspPlus_tsupport_horizontal h hx, cuspPlus_tsupport_radial h hx,
    cuspPlus_tsupport_vertical h hx⟩

/-- Reflected outgoing bounds; the lower normal coordinate is measured after reflection. -/
theorem cuspMinus_tsupport_outgoing_bounds {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspMinus) :
    x 0 ≤ p.R / 2 - p.normalCoordinate (reflection x) / 4 ∧
      p.R + p.normalCoordinate (reflection x) / 4 ≤ ‖x‖ ∧
      x 1 ≤ -(Real.sqrt 3 * p.R / 2) := by
  have href : reflection x ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
  have hb := cuspPlus_tsupport_horizontal_radial h href
  refine ⟨?_, ?_, cuspMinus_tsupport_vertical h hx⟩
  · simpa only [reflection, WithLp.ofLp_toLp, Matrix.cons_val_zero] using hb.1
  · simpa only [norm_reflection] using hb.2

/-- The radial action increases at least linearly along the upper cusp. -/
theorem cuspPlus_tsupport_radial_action_gain {p : CuspParameters} (h : p.BasicConditions)
    {E : ℝ} (hE : 0 < E) {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    Real.sqrt E * p.normalCoordinate x / 4 ≤
      bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R := by
  have ht := (cuspPlus_tsupport_subset_quadratic p hx).1
  have hr := cuspPlus_tsupport_radial h hx
  have hR : p.R ≤ ‖x‖ := by linarith
  have hgain := bridgeAction_sub_ge h.b_pos.ne' hE hR
  have hscale := mul_le_mul_of_nonneg_left
    (show p.normalCoordinate x / 4 ≤ ‖x‖ - p.R by linarith) (Real.sqrt_nonneg E)
  nlinarith

theorem cuspMinus_tsupport_radial_action_gain {p : CuspParameters} (h : p.BasicConditions)
    {E : ℝ} (hE : 0 < E) {x : Plane} (hx : x ∈ tsupport p.cuspMinus) :
    Real.sqrt E * p.normalCoordinate (reflection x) / 4 ≤
      bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R := by
  have href : reflection x ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
  simpa only [norm_reflection] using cuspPlus_tsupport_radial_action_gain h hE href

end InfiniteZero.CuspParameters
