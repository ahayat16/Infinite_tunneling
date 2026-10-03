import InfiniteZero.ComplexLandauKernel

/-!
# Effective real radii of small complex perturbations

The radius governing the absolute proper-time integrand is
`sqrt (Re ((r + δ)^2))`. On a fixed neighborhood of the positive real axis
it has the same real linear part as `r + δ`, with a uniform quadratic error.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

theorem re_sq_ofReal_add (r : ℝ) (δ : ℂ) :
    (((r : ℂ) + δ) ^ 2).re = (r + δ.re) ^ 2 - δ.im ^ 2 := by
  simp [pow_two, Complex.mul_re]

private theorem effectiveRadius_radicand_lower {r : ℝ} (hr : 0 < r) {δ : ℂ}
    (hδ : ‖δ‖ ≤ r / 4) : r ^ 2 / 2 ≤ (((r : ℂ) + δ) ^ 2).re := by
  have hre := (abs_le.mp (Complex.abs_re_le_norm δ)).1
  have him : δ.im ^ 2 ≤ ‖δ‖ ^ 2 := by
    nlinarith [Complex.sq_norm_sub_sq_re δ, sq_nonneg δ.re]
  have hn : ‖δ‖ ^ 2 ≤ r ^ 2 / 16 := by
    nlinarith [norm_nonneg δ]
  have hx : 3 * r / 4 ≤ r + δ.re := by linarith
  have hxsq : (3 * r / 4) ^ 2 ≤ (r + δ.re) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : 0 ≤ r + δ.re + 3 * r / 4)]
  rw [re_sq_ofReal_add]
  nlinarith

theorem re_sq_ofReal_add_pos {r : ℝ} (hr : 0 < r) {δ : ℂ}
    (hδ : ‖δ‖ ≤ r / 4) : 0 < (((r : ℂ) + δ) ^ 2).re :=
  (half_pos (sq_pos_of_pos hr)).trans_le (effectiveRadius_radicand_lower hr hδ)

theorem complexLandauEffectiveRadius_bounds {r : ℝ} (hr : 0 < r) {δ : ℂ}
    (hδ : ‖δ‖ ≤ r / 4) :
    complexLandauEffectiveRadius ((r : ℂ) + δ) ∈ Icc (r / 2) (r + ‖δ‖) := by
  let ρ := complexLandauEffectiveRadius ((r : ℂ) + δ)
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hs : ρ ^ 2 = (r + δ.re) ^ 2 - δ.im ^ 2 := by
    rw [← re_sq_ofReal_add]
    exact Real.sq_sqrt (re_sq_ofReal_add_pos hr hδ).le
  have hl := effectiveRadius_radicand_lower hr hδ
  rw [re_sq_ofReal_add] at hl
  have hre := abs_le.mp (Complex.abs_re_le_norm δ)
  have hx : 0 < r + δ.re := by linarith
  have hu : ρ ≤ r + δ.re := by nlinarith [sq_nonneg δ.im]
  exact ⟨by change r / 2 ≤ ρ; nlinarith, hu.trans (by linarith)⟩

private theorem effectiveRadius_denominator_lower {r : ℝ} (hr : 0 < r) {δ : ℂ}
    (hδ : ‖δ‖ ≤ r / 4) :
    r / 2 ≤ complexLandauEffectiveRadius ((r : ℂ) + δ) + r + δ.re := by
  have hρ := (complexLandauEffectiveRadius_bounds hr hδ).1
  have hre := (abs_le.mp (Complex.abs_re_le_norm δ)).1
  linarith

/-- Exact rationalized quadratic defect of the effective radius. -/
theorem complexLandauEffectiveRadius_sub_linear_eq {r : ℝ} (hr : 0 < r) {δ : ℂ}
    (hδ : ‖δ‖ ≤ r / 4) :
    complexLandauEffectiveRadius ((r : ℂ) + δ) - r - δ.re =
      -δ.im ^ 2 / (complexLandauEffectiveRadius ((r : ℂ) + δ) + r + δ.re) := by
  have hden : 0 < complexLandauEffectiveRadius ((r : ℂ) + δ) + r + δ.re :=
    (half_pos hr).trans_le (effectiveRadius_denominator_lower hr hδ)
  have hs : complexLandauEffectiveRadius ((r : ℂ) + δ) ^ 2 = (((r : ℂ) + δ) ^ 2).re :=
    Real.sq_sqrt (re_sq_ofReal_add_pos hr hδ).le
  rw [re_sq_ofReal_add] at hs
  apply (eq_div_iff hden.ne').2
  nlinarith

theorem abs_complexLandauEffectiveRadius_sub_linear_le {r : ℝ} (hr : 0 < r) {δ : ℂ}
    (hδ : ‖δ‖ ≤ r / 4) :
    |complexLandauEffectiveRadius ((r : ℂ) + δ) - r - δ.re| ≤ (2 / r) * ‖δ‖ ^ 2 := by
  have hden := effectiveRadius_denominator_lower hr hδ
  have hdenpos := (half_pos hr).trans_le hden
  have him : δ.im ^ 2 ≤ ‖δ‖ ^ 2 := by
    nlinarith [Complex.sq_norm_sub_sq_re δ, sq_nonneg δ.re]
  rw [complexLandauEffectiveRadius_sub_linear_eq hr hδ, abs_div, abs_neg,
    abs_of_nonneg (sq_nonneg _), abs_of_pos hdenpos]
  calc
    _ ≤ ‖δ‖ ^ 2 / (complexLandauEffectiveRadius ((r : ℂ) + δ) + r + δ.re) :=
      div_le_div_of_nonneg_right him hdenpos.le
    _ ≤ ‖δ‖ ^ 2 / (r / 2) := div_le_div_of_nonneg_left (sq_nonneg _) (half_pos hr) hden
    _ = _ := by ring

theorem abs_complexLandauEffectiveRadius_sub_le {r : ℝ} (hr : 0 < r) {δ : ℂ}
    (hδ : ‖δ‖ ≤ r / 4) :
    |complexLandauEffectiveRadius ((r : ℂ) + δ) - r| ≤ 2 * ‖δ‖ := by
  have hquad := abs_complexLandauEffectiveRadius_sub_linear_le hr hδ
  have hsmall : (2 / r) * ‖δ‖ ^ 2 ≤ ‖δ‖ / 2 := by
    calc
      _ ≤ (2 / r) * (‖δ‖ * (r / 4)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [sq] using mul_le_mul_of_nonneg_left hδ (norm_nonneg δ)
      _ = _ := by field_simp; ring
  have he : complexLandauEffectiveRadius ((r : ℂ) + δ) - r =
      (complexLandauEffectiveRadius ((r : ℂ) + δ) - r - δ.re) + δ.re := by ring
  rw [he]
  have := abs_add_le (complexLandauEffectiveRadius ((r : ℂ) + δ) - r - δ.re) δ.re
  linarith [Complex.abs_re_le_norm δ, norm_nonneg δ]

/-- The effective radii remain in a fixed positive real annulus, and the
quadratic constant is uniform in its base radius. -/
theorem complexLandauEffectiveRadius_uniform_bounds {rMin rMax r : ℝ}
    (hMin : 0 < rMin) (hr : r ∈ Icc rMin rMax) {δ : ℂ} (hδ : ‖δ‖ ≤ rMin / 4) :
    0 < (((r : ℂ) + δ) ^ 2).re ∧
    complexLandauEffectiveRadius ((r : ℂ) + δ) ∈ Icc (rMin / 2) (2 * rMax) ∧
    |complexLandauEffectiveRadius ((r : ℂ) + δ) - r - δ.re| ≤ (2 / rMin) * ‖δ‖ ^ 2 ∧
    |complexLandauEffectiveRadius ((r : ℂ) + δ) - r| ≤ 2 * ‖δ‖ := by
  have hrpos := hMin.trans_le hr.1
  have hδr : ‖δ‖ ≤ r / 4 := hδ.trans (by linarith [hr.1])
  have hb := complexLandauEffectiveRadius_bounds hrpos hδr
  refine ⟨re_sq_ofReal_add_pos hrpos hδr, ⟨by linarith [hb.1, hr.1],
    by linarith [hb.2, hr.1, hr.2]⟩, ?_, abs_complexLandauEffectiveRadius_sub_le hrpos hδr⟩
  apply (abs_complexLandauEffectiveRadius_sub_linear_le hrpos hδr).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact div_le_div_of_nonneg_left (by norm_num) hMin hr.1

/-- An epsilon-delta form of uniform continuity in the complex perturbation,
retaining the positive-annulus and quadratic-error information. -/
theorem exists_uniform_complexLandauEffectiveRadius_neighborhood {rMin rMax : ℝ}
    (hMin : 0 < rMin) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Icc rMin rMax, ∀ δ : ℂ, ‖δ‖ < ε →
      0 < (((r : ℂ) + δ) ^ 2).re ∧
      complexLandauEffectiveRadius ((r : ℂ) + δ) ∈ Icc (rMin / 2) (2 * rMax) ∧
      |complexLandauEffectiveRadius ((r : ℂ) + δ) - r - δ.re| ≤ (2 / rMin) * ‖δ‖ ^ 2 ∧
      |complexLandauEffectiveRadius ((r : ℂ) + δ) - r| < η := by
  refine ⟨min (rMin / 4) (η / 2), lt_min (by positivity) (half_pos hη), ?_⟩
  intro r hr δ hδ
  have hsmall := lt_min_iff.mp hδ
  obtain ⟨hp, hb, hq, hl⟩ := complexLandauEffectiveRadius_uniform_bounds hMin hr hsmall.1.le
  exact ⟨hp, hb, hq, by linarith [hsmall.2]⟩

/-- Uniform convergence for an arbitrarily varying real base radius bounded
away from zero; no convergence of that base radius is required. -/
theorem tendsto_complexLandauEffectiveRadius_sub_base {ι : Type*} {l : Filter ι}
    {r : ι → ℝ} {δ : ι → ℂ} {rMin : ℝ} (hMin : 0 < rMin)
    (hr : ∀ᶠ i in l, rMin ≤ r i) (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun i => complexLandauEffectiveRadius ((r i : ℂ) + δ i) - r i) l (𝓝 0) := by
  have hnorm : Tendsto (fun i => ‖δ i‖) l (𝓝 0) := by simpa using hδ.norm
  apply squeeze_zero_norm'
    (a := fun i => 2 * ‖δ i‖) ?_ (by simpa using hnorm.const_mul 2)
  filter_upwards [hr, hnorm.eventually (gt_mem_nhds (show (0 : ℝ) < rMin / 4 by positivity))]
    with i hri hdi
  rw [Real.norm_eq_abs]
  exact abs_complexLandauEffectiveRadius_sub_le (hMin.trans_le hri)
    (hdi.le.trans (by linarith))

end InfiniteZero
