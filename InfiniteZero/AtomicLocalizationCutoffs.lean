import InfiniteZero.ConstructionSupportSeparation
import InfiniteZero.MagneticIMS
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A fixed IMS partition for the constructed atomic potential

The inner cutoff equals one on the ball of radius `2 r₀` and vanishes
outside the ball of radius `3 r₀`. The outer cutoff is its smooth sine/cosine
partner. The entire partition is fixed before the semiclassical parameter.
The cusp supports start beyond `R/2 > 4 r₀`.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

def atomicLocalizationBump (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ContDiffBump (0 : Plane) where
  rIn := 2 * p.r₀
  rOut := 3 * p.r₀
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def atomicInnerCutoff (p : CuspParameters) (hr₀ : 0 < p.r₀) (x : Plane) : ℝ :=
  Real.sin (Real.pi / 2 * atomicLocalizationBump p hr₀ x)

def atomicOuterCutoff (p : CuspParameters) (hr₀ : 0 < p.r₀) (x : Plane) : ℝ :=
  Real.cos (Real.pi / 2 * atomicLocalizationBump p hr₀ x)

theorem atomicInnerCutoff_contDiff (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ContDiff ℝ ∞ (atomicInnerCutoff p hr₀) :=
  (contDiff_const.mul (atomicLocalizationBump p hr₀).contDiff).sin

theorem atomicOuterCutoff_contDiff (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ContDiff ℝ ∞ (atomicOuterCutoff p hr₀) :=
  (contDiff_const.mul (atomicLocalizationBump p hr₀).contDiff).cos

theorem atomicCutoffs_partition (p : CuspParameters) (hr₀ : 0 < p.r₀) (x : Plane) :
    atomicInnerCutoff p hr₀ x ^ 2 + atomicOuterCutoff p hr₀ x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

theorem atomicInnerCutoff_nonneg (p : CuspParameters) (hr₀ : 0 < p.r₀) (x : Plane) :
    0 ≤ atomicInnerCutoff p hr₀ x := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact mul_nonneg (by positivity) (atomicLocalizationBump p hr₀).nonneg
  · have hf := (atomicLocalizationBump p hr₀).le_one (x := x)
    nlinarith [Real.pi_pos]

theorem atomicInnerCutoff_le_one (p : CuspParameters) (hr₀ : 0 < p.r₀) (x : Plane) :
    atomicInnerCutoff p hr₀ x ≤ 1 := Real.sin_le_one _

theorem atomicLocalizationBump_one {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {x : Plane} (hx : ‖x‖ ≤ 2 * p.r₀) : atomicLocalizationBump p hr₀ x = 1 := by
  apply (atomicLocalizationBump p hr₀).one_of_mem_closedBall
  simpa [Metric.mem_closedBall, atomicLocalizationBump] using hx

theorem atomicLocalizationBump_zero {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {x : Plane} (hx : 3 * p.r₀ ≤ ‖x‖) : atomicLocalizationBump p hr₀ x = 0 := by
  apply (atomicLocalizationBump p hr₀).zero_of_le_dist
  simpa [atomicLocalizationBump] using hx

theorem atomicInnerCutoff_one {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {x : Plane} (hx : ‖x‖ ≤ 2 * p.r₀) : atomicInnerCutoff p hr₀ x = 1 := by
  simp [atomicInnerCutoff, atomicLocalizationBump_one hr₀ hx]

theorem atomicOuterCutoff_zero {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {x : Plane} (hx : ‖x‖ ≤ 2 * p.r₀) : atomicOuterCutoff p hr₀ x = 0 := by
  simp [atomicOuterCutoff, atomicLocalizationBump_one hr₀ hx]

theorem atomicInnerCutoff_zero {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {x : Plane} (hx : 3 * p.r₀ ≤ ‖x‖) : atomicInnerCutoff p hr₀ x = 0 := by
  simp [atomicInnerCutoff, atomicLocalizationBump_zero hr₀ hx]

theorem atomicOuterCutoff_one {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {x : Plane} (hx : 3 * p.r₀ ≤ ‖x‖) : atomicOuterCutoff p hr₀ x = 1 := by
  simp [atomicOuterCutoff, atomicLocalizationBump_zero hr₀ hx]

theorem atomicInnerCutoff_tsupport_subset (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    tsupport (atomicInnerCutoff p hr₀) ⊆ Metric.closedBall 0 (3 * p.r₀) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (atomicInnerCutoff_zero hr₀ (le_of_not_ge hn))

theorem atomicInnerCutoff_hasCompactSupport (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    HasCompactSupport (atomicInnerCutoff p hr₀) :=
  (isCompact_closedBall (0 : Plane) (3 * p.r₀)).of_isClosed_subset
    (isClosed_tsupport _) (atomicInnerCutoff_tsupport_subset p hr₀)

theorem atomicOuterCutoff_sub_one_hasCompactSupport (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    HasCompactSupport (fun x => atomicOuterCutoff p hr₀ x - 1) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Plane) (3 * p.r₀))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  simp [atomicOuterCutoff_one hr₀ (le_of_not_ge hx)]

/-- Both cusps vanish on the entire closed support of the inner localization. -/
theorem cusps_zero_on_atomicInnerCutoff_tsupport {p : CuspParameters}
    (hp : p.BasicConditions) {x : Plane} (hx : x ∈ tsupport (atomicInnerCutoff p hp.r₀_pos)) :
    p.cuspPlus x = 0 ∧ p.cuspMinus x = 0 := by
  have hn := atomicInnerCutoff_tsupport_subset p hp.r₀_pos hx
  rw [Metric.mem_closedBall, dist_zero_right] at hn
  constructor
  · by_contra hq
    have hnorm := cuspPlus_tsupport_norm_lower p (subset_tsupport _ hq)
    linarith [hp.radius_large, hp.r₀_pos]
  · by_contra hq
    have hnorm := cuspMinus_tsupport_norm_lower p (subset_tsupport _ hq)
    linarith [hp.radius_large, hp.r₀_pos]

theorem potential_mul_atomicInnerCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (x : Plane) : p.potential x * atomicInnerCutoff p hp.r₀_pos x =
      p.core x * atomicInnerCutoff p hp.r₀_pos x := by
  by_cases hx : atomicInnerCutoff p hp.r₀_pos x = 0
  · simp [hx]
  · obtain ⟨hplus, hminus⟩ := cusps_zero_on_atomicInnerCutoff_tsupport hp (subset_tsupport _ hx)
    simp [potential, hplus, hminus]

theorem core_mul_atomicOuterCutoff {p : CuspParameters} (hr₀ : 0 < p.r₀) (x : Plane) :
    p.core x * atomicOuterCutoff p hr₀ x = 0 := by
  by_cases hx : ‖x‖ ≤ 2 * p.r₀
  · rw [atomicOuterCutoff_zero hr₀ hx, mul_zero]
  · have hcore : p.core x = 0 := by
      simp [core, show ¬ ‖x‖ < p.r₀ by linarith]
    rw [hcore, zero_mul]

/-- Outside the radial well, the fixed cusp perturbation stays above -1/2. -/
theorem potential_exterior_gt_neg_half {p : CuspParameters} (hp : p.BasicConditions)
    {x : Plane} (hx : p.r₀ ≤ ‖x‖) : -(1 / 2 : ℝ) < p.potential x := by
  have hc : p.core x = 0 := by simp [core, not_lt.mpr hx]
  have hplus := (cuspPlus_range hp x).1
  have hminus := (cuspMinus_range hp x).1
  have hm := mul_le_mul_of_nonneg_left (show -2 * p.a ≤ p.cuspPlus x + p.cuspMinus x by
    linarith) hp.ε_pos.le
  rw [potential, hc]
  nlinarith [hp.depth_small]

private theorem exists_realPartialDerivative_bound {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C > 0, ∀ (i : Fin 2) (x : Plane), |realPartialDerivative i f x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := ((hc.fderiv ℝ).isCompact_range
    (hf.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun i x => ?_⟩
  have hn : ‖coordinateVector i‖ = 1 := by simp [coordinateVector]
  calc
    |realPartialDerivative i f x| = ‖fderiv ℝ f x (coordinateVector i)‖ := rfl
    _ ≤ ‖fderiv ℝ f x‖ * ‖coordinateVector i‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C := by rw [hn, mul_one]; exact hb _ ⟨x, rfl⟩

/-- The fixed partition has a globally bounded localization error. Its constant
does not depend on the field, coupling, energy or wavefunction. -/
theorem exists_atomicIMSError_bound (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ∃ C > 0, ∀ x, magneticIMSError (atomicInnerCutoff p hr₀)
      (atomicOuterCutoff p hr₀) x ≤ C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := exists_realPartialDerivative_bound
    (atomicInnerCutoff_contDiff p hr₀) (atomicInnerCutoff_hasCompactSupport p hr₀)
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_realPartialDerivative_bound
    ((atomicOuterCutoff_contDiff p hr₀).sub contDiff_const)
    (atomicOuterCutoff_sub_one_hasCompactSupport p hr₀)
  have hb₁' : ∀ (i : Fin 2) (x : Plane),
      |realPartialDerivative i (atomicOuterCutoff p hr₀) x| ≤ C₁ := by
    intro i x
    simpa only [realPartialDerivative, fderiv_sub_const] using hb₁ i x
  refine ⟨2 * (C₀ ^ 2 + C₁ ^ 2), by positivity, fun x => ?_⟩
  have hb (i : Fin 2) :
      realPartialDerivative i (atomicInnerCutoff p hr₀) x ^ 2 +
        realPartialDerivative i (atomicOuterCutoff p hr₀) x ^ 2 ≤ C₀ ^ 2 + C₁ ^ 2 := by
    have h₀ := (sq_le_sq₀ (abs_nonneg _) hC₀.le).mpr (hb₀ i x)
    have h₁ := (sq_le_sq₀ (abs_nonneg _) hC₁.le).mpr (hb₁' i x)
    simpa only [sq_abs] using add_le_add h₀ h₁
  simpa only [magneticIMSError, Fin.sum_univ_two, two_mul] using add_le_add (hb 0) (hb 1)

/-- The exterior potential has a fixed positive reserve below energies -3/4.
This is a property of the actual fixed potential, not an assumed spectral gap. -/
theorem atomicOuterCutoff_potential_lower {p : CuspParameters} (hp : p.BasicConditions)
    {e : ℝ} (he : e ≤ -(3 / 4 : ℝ)) (x : Plane) :
    (1 / 4 : ℝ) * atomicOuterCutoff p hp.r₀_pos x ^ 2 ≤
      (p.potential x - e) * atomicOuterCutoff p hp.r₀_pos x ^ 2 := by
  by_cases hx : ‖x‖ ≤ 2 * p.r₀
  · simp [atomicOuterCutoff_zero hp.r₀_pos hx]
  · have hv := potential_exterior_gt_neg_half hp (x := x) (by linarith [hp.r₀_pos])
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end InfiniteZero.CuspParameters
