import InfiniteZero.Construction

/-!
# Compact support of the explicit fixed potential

The cusp coordinates are inverted explicitly.  Their defining inequalities
then bound the support by a finite Euclidean ball, independently of both the
well separation and the coupling parameter.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

def cuspTip (p : CuspParameters) : Plane :=
  WithLp.toLp 2 ![p.R / 2, Real.sqrt 3 * p.R / 2]

def cuspNormal : Plane := WithLp.toLp 2 ![-1 / 2, Real.sqrt 3 / 2]

def cuspTangent : Plane := WithLp.toLp 2 ![-Real.sqrt 3 / 2, -1 / 2]

theorem norm_cuspNormal : ‖cuspNormal‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [cuspNormal, Fin.sum_univ_two, div_pow]

theorem norm_cuspTangent : ‖cuspTangent‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [cuspTangent, Fin.sum_univ_two, div_pow]

theorem cuspFrame_reconstruction (p : CuspParameters) (x : Plane) :
    x = p.cuspTip + p.normalCoordinate x • cuspNormal + p.tangentCoordinate x • cuspTangent := by
  have hcubic : (Real.sqrt (3 : ℝ)) ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ext i
  fin_cases i <;>
    simp [cuspTip, cuspNormal, cuspTangent, normalCoordinate, tangentCoordinate] <;>
    ring_nf <;> rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] <;>
    (try rw [hcubic]) <;> ring

theorem norm_le_cusp_coordinates (p : CuspParameters) (x : Plane) :
    ‖x‖ ≤ ‖p.cuspTip‖ + |p.normalCoordinate x| + |p.tangentCoordinate x| := by
  calc
    ‖x‖ = ‖p.cuspTip + p.normalCoordinate x • cuspNormal +
        p.tangentCoordinate x • cuspTangent‖ := congrArg norm (cuspFrame_reconstruction p x)
    _ ≤ ‖p.cuspTip + p.normalCoordinate x • cuspNormal‖ +
        ‖p.tangentCoordinate x • cuspTangent‖ := norm_add_le _ _
    _ ≤ (‖p.cuspTip‖ + ‖p.normalCoordinate x • cuspNormal‖) +
        ‖p.tangentCoordinate x • cuspTangent‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by simp [norm_smul, Real.norm_eq_abs, norm_cuspNormal, norm_cuspTangent]

def cuspSupportRadius (p : CuspParameters) : ℝ :=
  ‖p.cuspTip‖ + p.t₀ + p.s₀ * p.t₀ ^ 2

theorem cuspPlus_norm_bound {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : p.cuspPlus x ≠ 0) : ‖x‖ ≤ p.cuspSupportRadius := by
  have hc : 0 < p.normalCoordinate x ∧ p.normalCoordinate x < p.t₀ ∧
      |p.tangentCoordinate x / p.normalCoordinate x ^ 2| < p.s₀ := by
    by_contra hn
    exact hx (by simp [cuspPlus, hn])
  have ht2 : 0 < p.normalCoordinate x ^ 2 := sq_pos_of_pos hc.1
  have hu : |p.tangentCoordinate x| < p.s₀ * p.normalCoordinate x ^ 2 := by
    apply (div_lt_iff₀ ht2).mp
    simpa only [abs_div, abs_of_pos ht2] using hc.2.2
  have htbound : p.normalCoordinate x ^ 2 ≤ p.t₀ ^ 2 := by
    nlinarith [hc.1, hc.2.1, h.t₀_pos]
  have hubound : |p.tangentCoordinate x| ≤ p.s₀ * p.t₀ ^ 2 :=
    hu.le.trans (mul_le_mul_of_nonneg_left htbound h.s₀_pos.le)
  have hn := norm_le_cusp_coordinates p x
  rw [abs_of_pos hc.1] at hn
  unfold cuspSupportRadius
  linarith [hc.2.1]

theorem cuspMinus_norm_bound {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : p.cuspMinus x ≠ 0) : ‖x‖ ≤ p.cuspSupportRadius := by
  have hn := cuspPlus_norm_bound h (x := reflection x) hx
  simpa only [norm_reflection] using hn

theorem core_hasCompactSupport (p : CuspParameters) : HasCompactSupport p.core := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) p.r₀)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hx' : p.core x ≠ 0 := hx
  by_contra hn
  exact hx' (by simp [core, not_lt.mpr (le_of_not_ge hn)])

theorem cuspPlus_hasCompactSupport {p : CuspParameters} (h : p.BasicConditions) :
    HasCompactSupport p.cuspPlus := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Plane) p.cuspSupportRadius)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact cuspPlus_norm_bound h hx

theorem cuspMinus_hasCompactSupport {p : CuspParameters} (h : p.BasicConditions) :
    HasCompactSupport p.cuspMinus := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Plane) p.cuspSupportRadius)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact cuspMinus_norm_bound h hx

/-- Compact support requires only the elementary parameter conditions; no
smoothness, PDE input, or asymptotic estimate is used. -/
theorem potential_hasCompactSupport {p : CuspParameters} (h : p.BasicConditions) :
    HasCompactSupport p.potential := by
  have hsum : HasCompactSupport (p.cuspPlus + p.cuspMinus) :=
    (cuspPlus_hasCompactSupport h).add (cuspMinus_hasCompactSupport h)
  have hscaled : HasCompactSupport (fun x => p.ε * (p.cuspPlus x + p.cuspMinus x)) :=
    hsum.mul_left
  exact (core_hasCompactSupport p).add hscaled

end InfiniteZero.CuspParameters
