import InfiniteZero.AtomicLocalizationCutoffs
import InfiniteZero.MagneticLocalEnergy

/-!
# A fixed smooth bounded Agmon weight

The transition is between radii `3 r₀` and `4 r₀`. Its height is `d * coupling`,
where `d > 0` is chosen once from a derivative bound for a fixed bump. The
weight vanishes wherever the outer IMS cutoff has a nonzero derivative.
-/

noncomputable section
open Set
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

def atomicAgmonBump (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ContDiffBump (0 : Plane) where
  rIn := 3 * p.r₀
  rOut := 4 * p.r₀
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

private theorem exists_atomicAgmonDerivativeBound (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ∃ C > 0, ∀ (i : Fin 2) (x : Plane),
      |realPartialDerivative i (atomicAgmonBump p hr₀) x| ≤ C := by
  let f := atomicAgmonBump p hr₀
  have hf : ContDiff ℝ ∞ (f : Plane → ℝ) := f.contDiff
  obtain ⟨C, hC, hb⟩ := ((f.hasCompactSupport.fderiv ℝ).isCompact_range
    (hf.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun i x => ?_⟩
  have hn : ‖coordinateVector i‖ = 1 := by simp [coordinateVector]
  calc
    |realPartialDerivative i (atomicAgmonBump p hr₀) x| =
        ‖fderiv ℝ f x (coordinateVector i)‖ := rfl
    _ ≤ ‖fderiv ℝ f x‖ * ‖coordinateVector i‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C := by rw [hn, mul_one]; exact hb _ ⟨x, rfl⟩

/-- A derivative bound chosen before the coupling parameter. -/
def atomicAgmonDerivativeBound (p : CuspParameters) (hr₀ : 0 < p.r₀) : ℝ :=
  Classical.choose (exists_atomicAgmonDerivativeBound p hr₀)

theorem atomicAgmonDerivativeBound_pos (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    0 < atomicAgmonDerivativeBound p hr₀ :=
  (Classical.choose_spec (exists_atomicAgmonDerivativeBound p hr₀)).1

theorem atomicAgmonBump_partial_bound (p : CuspParameters) (hr₀ : 0 < p.r₀)
    (i : Fin 2) (x : Plane) :
    |realPartialDerivative i (atomicAgmonBump p hr₀) x| ≤
      atomicAgmonDerivativeBound p hr₀ :=
  (Classical.choose_spec (exists_atomicAgmonDerivativeBound p hr₀)).2 i x

/-- Fixed positive height per unit coupling; independent of the coupling. -/
def atomicAgmonRate (p : CuspParameters) (hr₀ : 0 < p.r₀) : ℝ :=
  1 / (8 * atomicAgmonDerivativeBound p hr₀)

theorem atomicAgmonRate_pos (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    0 < atomicAgmonRate p hr₀ := by
  unfold atomicAgmonRate
  exact one_div_pos.mpr (mul_pos (by norm_num) (atomicAgmonDerivativeBound_pos p hr₀))

def atomicAgmonWeight (p : CuspParameters) (hr₀ : 0 < p.r₀) (coupling : ℝ)
    (x : Plane) : ℝ :=
  atomicAgmonRate p hr₀ * coupling * (1 - atomicAgmonBump p hr₀ x)

theorem atomicAgmonWeight_contDiff (p : CuspParameters) (hr₀ : 0 < p.r₀)
    (coupling : ℝ) : ContDiff ℝ ∞ (atomicAgmonWeight p hr₀ coupling) :=
  contDiff_const.mul (contDiff_const.sub (atomicAgmonBump p hr₀).contDiff)

theorem atomicAgmonWeight_nonneg (p : CuspParameters) (hr₀ : 0 < p.r₀)
    {coupling : ℝ} (hc : 0 ≤ coupling) (x : Plane) :
    0 ≤ atomicAgmonWeight p hr₀ coupling x := by
  exact mul_nonneg (mul_nonneg (atomicAgmonRate_pos p hr₀).le hc)
    (sub_nonneg.mpr (atomicAgmonBump p hr₀).le_one)

theorem atomicAgmonWeight_le (p : CuspParameters) (hr₀ : 0 < p.r₀)
    {coupling : ℝ} (hc : 0 ≤ coupling) (x : Plane) :
    atomicAgmonWeight p hr₀ coupling x ≤ atomicAgmonRate p hr₀ * coupling := by
  apply mul_le_of_le_one_right (mul_nonneg (atomicAgmonRate_pos p hr₀).le hc)
  linarith [(atomicAgmonBump p hr₀).nonneg (x := x)]

theorem atomicAgmonWeight_abs_le (p : CuspParameters) (hr₀ : 0 < p.r₀)
    (coupling : ℝ) (x : Plane) :
    |atomicAgmonWeight p hr₀ coupling x| ≤ atomicAgmonRate p hr₀ * |coupling| := by
  have hb : |1 - atomicAgmonBump p hr₀ x| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (atomicAgmonBump p hr₀).le_one)]
    linarith [(atomicAgmonBump p hr₀).nonneg (x := x)]
  unfold atomicAgmonWeight
  rw [abs_mul, abs_mul, abs_of_pos (atomicAgmonRate_pos p hr₀)]
  exact mul_le_of_le_one_right (mul_nonneg (atomicAgmonRate_pos p hr₀).le (abs_nonneg _)) hb

theorem atomicAgmonWeight_zero {p : CuspParameters} (hr₀ : 0 < p.r₀)
    (coupling : ℝ) {x : Plane} (hx : ‖x‖ ≤ 3 * p.r₀) :
    atomicAgmonWeight p hr₀ coupling x = 0 := by
  have hb : atomicAgmonBump p hr₀ x = 1 := by
    apply (atomicAgmonBump p hr₀).one_of_mem_closedBall
    simpa [Metric.mem_closedBall, atomicAgmonBump] using hx
  simp [atomicAgmonWeight, hb]

theorem atomicAgmonWeight_eq_height {p : CuspParameters} (hr₀ : 0 < p.r₀)
    (coupling : ℝ) {x : Plane} (hx : 4 * p.r₀ ≤ ‖x‖) :
    atomicAgmonWeight p hr₀ coupling x = atomicAgmonRate p hr₀ * coupling := by
  have hb : atomicAgmonBump p hr₀ x = 0 := by
    apply (atomicAgmonBump p hr₀).zero_of_le_dist
    simpa [atomicAgmonBump] using hx
  simp [atomicAgmonWeight, hb]

theorem atomicAgmonWeight_partial (p : CuspParameters) (hr₀ : 0 < p.r₀)
    (coupling : ℝ) (i : Fin 2) (x : Plane) :
    realPartialDerivative i (atomicAgmonWeight p hr₀ coupling) x =
      -(atomicAgmonRate p hr₀ * coupling) *
        realPartialDerivative i (atomicAgmonBump p hr₀) x := by
  have hf : ContDiff ℝ ∞ (atomicAgmonBump p hr₀ : Plane → ℝ) :=
    (atomicAgmonBump p hr₀).contDiff
  have hb := (hf.differentiable (by simp)) x
  change (fderiv ℝ (fun y => (atomicAgmonRate p hr₀ * coupling) *
    (1 - atomicAgmonBump p hr₀ y)) x) (coordinateVector i) =
      -(atomicAgmonRate p hr₀ * coupling) *
        (fderiv ℝ (atomicAgmonBump p hr₀ : Plane → ℝ) x) (coordinateVector i)
  rw [fderiv_const_mul (hb.const_sub 1), fderiv_const_sub]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  ring

theorem atomicAgmonWeight_partial_bound (p : CuspParameters) (hr₀ : 0 < p.r₀)
    {coupling : ℝ} (hc : 0 ≤ coupling) (i : Fin 2) (x : Plane) :
    |realPartialDerivative i (atomicAgmonWeight p hr₀ coupling) x| ≤ coupling / 8 := by
  rw [atomicAgmonWeight_partial, abs_mul, abs_neg,
    abs_of_nonneg (mul_nonneg (atomicAgmonRate_pos p hr₀).le hc)]
  calc
    _ ≤ (atomicAgmonRate p hr₀ * coupling) * atomicAgmonDerivativeBound p hr₀ :=
      mul_le_mul_of_nonneg_left (atomicAgmonBump_partial_bound p hr₀ i x)
        (mul_nonneg (atomicAgmonRate_pos p hr₀).le hc)
    _ = coupling / 8 := by
      unfold atomicAgmonRate
      field_simp [(atomicAgmonDerivativeBound_pos p hr₀).ne']

theorem atomicAgmonWeight_gradient_le (p : CuspParameters) (hr₀ : 0 < p.r₀)
    {coupling : ℝ} (hc : 0 ≤ coupling) (x : Plane) :
    cutoffGradientSq (atomicAgmonWeight p hr₀ coupling) x ≤ coupling ^ 2 / 16 := by
  have hb (i : Fin 2) :
      realPartialDerivative i (atomicAgmonWeight p hr₀ coupling) x ^ 2 ≤
        (coupling / 8) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ coupling / 8)).mpr
      (atomicAgmonWeight_partial_bound p hr₀ hc i x)
    simpa only [sq_abs] using this
  simp only [cutoffGradientSq, Fin.sum_univ_two]
  nlinarith [hb 0, hb 1, sq_nonneg coupling]

theorem atomicOuterCutoff_gradient_zero_of_norm_gt {p : CuspParameters}
    (hr₀ : 0 < p.r₀) {x : Plane} (hx : 3 * p.r₀ < ‖x‖) :
    cutoffGradientSq (atomicOuterCutoff p hr₀) x = 0 := by
  have he : atomicOuterCutoff p hr₀ =ᶠ[𝓝 x] (fun _ : Plane => (1 : ℝ)) := by
    have hs : IsOpen {y : Plane | 3 * p.r₀ < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hs.mem_nhds hx] with y hy
    exact atomicOuterCutoff_one hr₀ hy.le
  have hd : fderiv ℝ (atomicOuterCutoff p hr₀) x = 0 := by
    rw [he.fderiv_eq]
    exact fderiv_const_apply 1
  simp [cutoffGradientSq, realPartialDerivative, hd]

/-- The weight is zero on the region that contributes to the IMS error. -/
theorem atomicAgmonWeight_zero_of_outer_gradient_ne_zero {p : CuspParameters}
    (hr₀ : 0 < p.r₀) (coupling : ℝ) {x : Plane}
    (hx : cutoffGradientSq (atomicOuterCutoff p hr₀) x ≠ 0) :
    atomicAgmonWeight p hr₀ coupling x = 0 := by
  apply atomicAgmonWeight_zero hr₀ coupling
  by_contra hn
  exact hx (atomicOuterCutoff_gradient_zero_of_norm_gt hr₀ (lt_of_not_ge hn))

theorem exp_atomicAgmonWeight_sq_mul_outer_gradient (p : CuspParameters)
    (hr₀ : 0 < p.r₀) (coupling : ℝ) (x : Plane) :
    Real.exp (atomicAgmonWeight p hr₀ coupling x) ^ 2 *
        cutoffGradientSq (atomicOuterCutoff p hr₀) x =
      cutoffGradientSq (atomicOuterCutoff p hr₀) x := by
  by_cases hx : cutoffGradientSq (atomicOuterCutoff p hr₀) x = 0
  · simp [hx]
  · rw [atomicAgmonWeight_zero_of_outer_gradient_ne_zero hr₀ coupling hx]
    simp

end InfiniteZero.CuspParameters
