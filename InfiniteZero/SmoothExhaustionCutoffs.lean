import InfiniteZero.MagneticLocalEnergy
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Smooth cutoffs exhausting the plane

A fixed bump equal to one on the unit ball is rescaled by `R⁻¹`.
Its squared gradient scales exactly by `R⁻²`; hence the gradient bound
has a constant independent of both the radius and the point.
-/

noncomputable section
open Set
open scoped ContDiff Topology

namespace InfiniteZero

def exhaustionBump : ContDiffBump (0 : Plane) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def smoothExhaustionCutoff (R : ℝ) (x : Plane) : ℝ :=
  exhaustionBump (R⁻¹ • x)

theorem smoothExhaustionCutoff_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (smoothExhaustionCutoff R) := by
  change ContDiff ℝ ∞ (fun x : Plane => exhaustionBump (R⁻¹ • x))
  exact exhaustionBump.contDiff.comp (contDiff_id.const_smul R⁻¹)

theorem smoothExhaustionCutoff_range (R : ℝ) (x : Plane) :
    smoothExhaustionCutoff R x ∈ Icc (0 : ℝ) 1 :=
  ⟨exhaustionBump.nonneg, exhaustionBump.le_one⟩

theorem smoothExhaustionCutoff_one {R : ℝ} (hR : 0 < R)
    {x : Plane} (hx : ‖x‖ ≤ R) : smoothExhaustionCutoff R x = 1 := by
  apply exhaustionBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hR, exhaustionBump]
  exact (inv_mul_le_iff₀ hR).mpr (by simpa using hx)

theorem smoothExhaustionCutoff_zero {R : ℝ} (hR : 0 < R)
    {x : Plane} (hx : 2 * R ≤ ‖x‖) : smoothExhaustionCutoff R x = 0 := by
  apply exhaustionBump.zero_of_le_dist
  simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hR, exhaustionBump]
  exact (le_inv_mul_iff₀ hR).mpr (by linarith)

theorem smoothExhaustionCutoff_tsupport_subset {R : ℝ} (hR : 0 < R) :
    tsupport (smoothExhaustionCutoff R) ⊆ Metric.closedBall 0 (2 * R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (smoothExhaustionCutoff_zero hR (le_of_not_ge hn))

theorem smoothExhaustionCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (smoothExhaustionCutoff R) :=
  (isCompact_closedBall (0 : Plane) (2 * R)).of_isClosed_subset
    (isClosed_tsupport _) (smoothExhaustionCutoff_tsupport_subset hR)

theorem smoothExhaustionCutoff_realPartialDerivative (R : ℝ) (i : Fin 2) (x : Plane) :
    realPartialDerivative i (smoothExhaustionCutoff R) x =
      R⁻¹ * realPartialDerivative i exhaustionBump (R⁻¹ • x) := by
  change fderiv ℝ (fun y : Plane => exhaustionBump (R⁻¹ • y)) x (coordinateVector i) = _
  simp only [fderiv_comp_smul, realPartialDerivative,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem smoothExhaustionCutoff_realPartialDerivative_zero {R : ℝ} (hR : 0 < R)
    {x : Plane} (hx : ‖x‖ < R) (i : Fin 2) :
    realPartialDerivative i (smoothExhaustionCutoff R) x = 0 := by
  have heq : smoothExhaustionCutoff R =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
    exact smoothExhaustionCutoff_one hR hy.le
  simp only [realPartialDerivative, heq.fderiv_eq, fderiv_const_apply,
    ContinuousLinearMap.zero_apply]

theorem smoothExhaustionCutoff_gradientSq_zero {R : ℝ} (hR : 0 < R)
    {x : Plane} (hx : ‖x‖ < R) :
    cutoffGradientSq (smoothExhaustionCutoff R) x = 0 := by
  simp only [cutoffGradientSq, smoothExhaustionCutoff_realPartialDerivative_zero hR hx,
    zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]

/-- Exact scaling, including the totalized definition at `R = 0`. -/
theorem smoothExhaustionCutoff_gradientSq (R : ℝ) (x : Plane) :
    cutoffGradientSq (smoothExhaustionCutoff R) x =
      (R⁻¹) ^ 2 * cutoffGradientSq exhaustionBump (R⁻¹ • x) := by
  simp only [cutoffGradientSq, smoothExhaustionCutoff_realPartialDerivative,
    mul_pow, Finset.mul_sum]

/-- The fixed base bump has a bounded gradient on the whole plane. -/
theorem exists_exhaustionBump_gradient_bound :
    ∃ C ≥ 0, ∀ x, cutoffGradientSq exhaustionBump x ≤ C := by
  have hbase : ContDiff ℝ ∞ (exhaustionBump : Plane → ℝ) := exhaustionBump.contDiff
  obtain ⟨B, hB, hb⟩ := ((exhaustionBump.hasCompactSupport.fderiv ℝ).isCompact_range
    (hbase.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  have hpartial (i : Fin 2) (x : Plane) :
      |realPartialDerivative i exhaustionBump x| ≤ B := by
    calc
      |realPartialDerivative i exhaustionBump x| =
          ‖fderiv ℝ exhaustionBump x (coordinateVector i)‖ := rfl
      _ ≤ ‖fderiv ℝ exhaustionBump x‖ * ‖coordinateVector i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ B := by
        have hn : ‖coordinateVector i‖ = 1 := by simp [coordinateVector]
        rw [hn, mul_one]
        exact hb _ ⟨x, rfl⟩
  refine ⟨2 * B ^ 2, by positivity, fun x => ?_⟩
  have hs (i : Fin 2) : realPartialDerivative i exhaustionBump x ^ 2 ≤ B ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hB.le).mpr (hpartial i x)
    simpa only [sq_abs] using h
  simpa only [cutoffGradientSq, Fin.sum_univ_two, two_mul] using add_le_add (hs 0) (hs 1)

/-- The gradient constant is fixed before the radius is chosen. -/
theorem exists_smoothExhaustionCutoff_gradient_bound :
    ∃ C ≥ 0, ∀ R : ℝ, 0 < R → ∀ x,
      cutoffGradientSq (smoothExhaustionCutoff R) x ≤ C / R ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_exhaustionBump_gradient_bound
  refine ⟨C, hC, fun R _ x => ?_⟩
  rw [smoothExhaustionCutoff_gradientSq]
  calc
    (R⁻¹) ^ 2 * cutoffGradientSq exhaustionBump (R⁻¹ • x) ≤ (R⁻¹) ^ 2 * C :=
      mul_le_mul_of_nonneg_left (hb _) (sq_nonneg _)
    _ = C / R ^ 2 := by simp only [div_eq_mul_inv, inv_pow]; ring

end InfiniteZero
