import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-!
# Fixed-width smooth cutoffs on an exterior half-line

The inner transition is fixed and the outer transition moves to infinity.
Both transitions have width one, so the derivative bound is independent of
the outer endpoint. These cutoffs are intended for interval Caccioppoli
estimates, with endpoints at which the cutoff vanishes exactly.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero

def radialExteriorCutoff (a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  Real.smoothTransition (r - a - 1) *
    Real.smoothTransition (a + (n : ℝ) + 3 - r)

theorem radialExteriorCutoff_contDiff (a : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (radialExteriorCutoff a n) := by
  unfold radialExteriorCutoff
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem radialExteriorCutoff_range (a : ℝ) (n : ℕ) (r : ℝ) :
    radialExteriorCutoff a n r ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)

theorem radialExteriorCutoff_zero_left (a : ℝ) (n : ℕ) {r : ℝ} (hr : r ≤ a + 1) :
    radialExteriorCutoff a n r = 0 := by
  unfold radialExteriorCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : r - a - 1 ≤ 0), zero_mul]

theorem radialExteriorCutoff_zero_right (a : ℝ) (n : ℕ) {r : ℝ}
    (hr : a + (n : ℝ) + 3 ≤ r) : radialExteriorCutoff a n r = 0 := by
  unfold radialExteriorCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : a + (n : ℝ) + 3 - r ≤ 0),
    mul_zero]

theorem radialExteriorCutoff_one (a : ℝ) (n : ℕ) {r : ℝ}
    (hlo : a + 2 ≤ r) (hhi : r ≤ a + (n : ℝ) + 2) :
    radialExteriorCutoff a n r = 1 := by
  unfold radialExteriorCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ r - a - 1),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ a + (n : ℝ) + 3 - r), one_mul]

theorem radialExteriorCutoff_hasCompactSupport (a : ℝ) (n : ℕ) :
    HasCompactSupport (radialExteriorCutoff a n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (a + 1) (a + (n : ℝ) + 3)))
  intro r hr
  constructor
  · by_contra hlo
    exact hr (radialExteriorCutoff_zero_left a n (le_of_not_ge hlo))
  · by_contra hhi
    exact hr (radialExteriorCutoff_zero_right a n (le_of_not_ge hhi))

theorem continuous_deriv_radialExteriorCutoff (a : ℝ) (n : ℕ) :
    Continuous (deriv (radialExteriorCutoff a n)) :=
  (radialExteriorCutoff_contDiff a n).continuous_deriv (by simp)

theorem hasDerivAt_radialExteriorCutoff (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (radialExteriorCutoff a n)
      (deriv Real.smoothTransition (r - a - 1) *
        Real.smoothTransition (a + (n : ℝ) + 3 - r) -
        Real.smoothTransition (r - a - 1) *
          deriv Real.smoothTransition (a + (n : ℝ) + 3 - r)) r := by
  have hd (x : ℝ) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
      (by simp) x).hasDerivAt
  have hl := (hd (r - a - 1)).comp r (((hasDerivAt_id r).sub_const a).sub_const 1)
  have hr := (hd (a + (n : ℝ) + 3 - r)).comp r
    ((hasDerivAt_id r).const_sub (a + (n : ℝ) + 3))
  convert hl.mul hr using 1
  simp only [Function.comp_apply, id_eq, mul_one, sub_eq_add_neg, mul_neg]

private theorem exists_smoothTransition_deriv_bound :
    ∃ D > 0, ∀ r : ℝ, |deriv Real.smoothTransition r| ≤ D := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv
      (by simp)
  obtain ⟨D, hD, hbound⟩ := (isCompact_Icc.image hc).isBounded.exists_pos_norm_le
  refine ⟨D, hD, ?_⟩
  intro r
  by_cases hr : r ∈ Icc (0 : ℝ) 1
  · simpa only [Real.norm_eq_abs] using hbound _ ⟨r, hr, rfl⟩
  · have hd : deriv Real.smoothTransition r = 0 := by
      rcases not_and_or.mp hr with hlo | hhi
      · have heq : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
          filter_upwards [eventually_lt_nhds (lt_of_not_ge hlo)] with x hx
          exact Real.smoothTransition.zero_of_nonpos hx.le
        rw [heq.deriv_eq]
        exact deriv_const r 0
      · have heq : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
          filter_upwards [eventually_gt_nhds (lt_of_not_ge hhi)] with x hx
          exact Real.smoothTransition.one_of_one_le hx.le
        rw [heq.deriv_eq]
        exact deriv_const r 1
    rw [hd, abs_zero]
    exact hD.le

/-- One bound works for every outer endpoint of the exhaustion. -/
theorem exists_radialExteriorCutoff_deriv_bound (a : ℝ) :
    ∃ D > 0, ∀ n : ℕ, ∀ r : ℝ, |deriv (radialExteriorCutoff a n) r| ≤ D := by
  obtain ⟨D, hD, hbound⟩ := exists_smoothTransition_deriv_bound
  refine ⟨2 * D, by positivity, ?_⟩
  intro n r
  rw [(hasDerivAt_radialExteriorCutoff a n r).deriv]
  calc
    _ ≤ |deriv Real.smoothTransition (r - a - 1) *
          Real.smoothTransition (a + (n : ℝ) + 3 - r)| +
        |Real.smoothTransition (r - a - 1) *
          deriv Real.smoothTransition (a + (n : ℝ) + 3 - r)| := abs_sub _ _
    _ ≤ D * 1 + 1 * D := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (Real.smoothTransition.nonneg (a + (n : ℝ) + 3 - r)),
        abs_of_nonneg (Real.smoothTransition.nonneg (r - a - 1))]
      exact add_le_add
        (mul_le_mul (hbound _) (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _) hD.le)
        (mul_le_mul (Real.smoothTransition.le_one _) (hbound _) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- Every fixed point beyond the inner transition eventually lies on the plateau. -/
theorem eventually_radialExteriorCutoff_eq_one (a : ℝ) {r : ℝ} (hr : a + 2 ≤ r) :
    ∀ᶠ n : ℕ in atTop, radialExteriorCutoff a n r = 1 := by
  have hn : ∀ᶠ n : ℕ in atTop, r - a - 2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  exact hn.mono fun n hn => radialExteriorCutoff_one a n hr (by linarith)

theorem tendsto_radialExteriorCutoff (a : ℝ) {r : ℝ} (hr : a + 2 ≤ r) :
    Tendsto (fun n : ℕ => radialExteriorCutoff a n r) atTop (𝓝 1) :=
  tendsto_const_nhds.congr'
    ((eventually_radialExteriorCutoff_eq_one a hr).mono fun _ hn => hn.symm)

end InfiniteZero
