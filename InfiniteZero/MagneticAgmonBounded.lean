import InfiniteZero.CutoffGradientProduct
import InfiniteZero.SmoothExhaustionCutoffs
import InfiniteZero.EigenfunctionCutoffLimits

/-!
# Removal of spatial cutoffs for a bounded smooth Agmon weight

Only the eigenfunction's L² norm is used for domination. The actual smooth
exhaustion has a uniform gradient bound and is locally constant eventually.
-/

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace InfiniteZero

theorem eventually_smoothExhaustion_radius (x : Plane) :
    ∀ᶠ n : ℕ in atTop, ‖x‖ < (n : ℝ) + 1 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact ht.eventually (eventually_gt_atTop ‖x‖)

/-- A bounded smooth exponential weight can be used with a noncompact
exterior cutoff. This is proved by removing compact spatial cutoffs, without
assuming a global differential energy integral for the eigenfunction. -/
theorem magnetic_agmon_bounded_weight {b coupling E δ B Cσ : ℝ} {V : Potential}
    {σ F : Plane → ℝ} {φ : Wavefunction} (hV : Continuous V)
    (hσ : ContDiff ℝ ∞ σ) (hσbound : ∀ x, |σ x| ≤ 1)
    (hCσ : 0 ≤ Cσ) (hσgrad : ∀ x, cutoffGradientSq σ x ≤ Cσ)
    (hF : ContDiff ℝ ∞ F) (hFbound : ∀ x, F x ≤ B)
    (hφ : IsEigenfunction b coupling V E φ)
    (hreserve : ∀ x, σ x ≠ 0 → δ ≤ coupling ^ 2 * V x - E - 2 * cutoffGradientSq F x) :
    δ * mass (fun x => ((σ x * Real.exp (F x) : ℝ) : ℂ) * φ x) ≤
      2 * ∫ x : Plane, Real.exp (F x) ^ 2 * cutoffGradientSq σ x * ‖φ x‖ ^ 2 := by
  let κ : ℕ → Plane → ℝ := fun n => smoothExhaustionCutoff ((n : ℝ) + 1)
  let η : ℕ → Plane → ℝ := fun n x => σ x * κ n x
  have hR (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hκ (n : ℕ) : ContDiff ℝ ∞ (κ n) := smoothExhaustionCutoff_contDiff _
  have hη (n : ℕ) : ContDiff ℝ ∞ (η n) := hσ.mul (hκ n)
  have hηc (n : ℕ) : HasCompactSupport (η n) :=
    (smoothExhaustionCutoff_hasCompactSupport (hR n)).mul_left
  have hκabs (n : ℕ) (x : Plane) : |κ n x| ≤ 1 := by
    have hr := smoothExhaustionCutoff_range ((n : ℝ) + 1) x
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hηabs (n : ℕ) (x : Plane) : |η n x| ≤ 1 := by
    rw [show η n x = σ x * κ n x from rfl, abs_mul]
    exact (mul_le_mul (hσbound x) (hκabs n x) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hηlim (x : Plane) : ∀ᶠ n : ℕ in atTop, η n x = σ x := by
    filter_upwards [eventually_smoothExhaustion_radius x] with n hn
    have hone : κ n x = 1 := smoothExhaustionCutoff_one (hR n) hn.le
    simp only [η, hone, mul_one]
  have hgradlim (x : Plane) :
      ∀ᶠ n : ℕ in atTop, cutoffGradientSq (η n) x = cutoffGradientSq σ x := by
    filter_upwards [eventually_smoothExhaustion_radius x] with n hn
    exact cutoffGradientSq_mul_eq_of_one ((hσ.differentiable (by simp)) x)
      (((hκ n).differentiable (by simp)) x)
      (smoothExhaustionCutoff_one (hR n) hn.le)
      (fun i => smoothExhaustionCutoff_realPartialDerivative_zero (hR n) hn i)
  obtain ⟨Cκ, hCκ, hκgrad⟩ := exists_smoothExhaustionCutoff_gradient_bound
  have hκgrad' (n : ℕ) (x : Plane) : cutoffGradientSq (κ n) x ≤ Cκ := by
    apply (hκgrad ((n : ℝ) + 1) (hR n) x).trans
    apply (div_le_iff₀ (sq_pos_of_pos (hR n))).mpr
    have hr : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa using mul_le_mul_of_nonneg_left hr hCκ
  have hηgrad (n : ℕ) (x : Plane) : cutoffGradientSq (η n) x ≤ 2 * Cσ + 2 * Cκ := by
    have hb := cutoffGradientSq_mul_le ((hσ.differentiable (by simp)) x)
      (((hκ n).differentiable (by simp)) x)
    have hσsq : σ x ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (abs_nonneg (σ x)) zero_le_one).mpr (hσbound x)
    have hκsq : κ n x ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (abs_nonneg (κ n x)) zero_le_one).mpr (hκabs n x)
    have h₁ := mul_le_mul hκsq (hσgrad x) (cutoffGradientSq_nonneg σ x) zero_le_one
    have h₂ := mul_le_mul hσsq (hκgrad' n x) (cutoffGradientSq_nonneg (κ n) x) zero_le_one
    change cutoffGradientSq (fun y => σ y * κ n y) x ≤ _
    nlinarith only [hb, h₁, h₂]
  have hexp (x : Plane) : Real.exp (F x) ≤ Real.exp B := Real.exp_le_exp.mpr (hFbound x)
  have hmass : Tendsto (fun n => mass (fun x => ((η n x * Real.exp (F x) : ℝ) : ℂ) * φ x))
      atTop (𝓝 (mass (fun x => ((σ x * Real.exp (F x) : ℝ) : ℂ) * φ x))) := by
    apply tendsto_mass_real_cutoff_of_bounded hφ.2.1
      (c := fun n x => η n x * Real.exp (F x))
      (fun n => ((hη n).continuous.mul hF.exp.continuous).measurable)
      (C := Real.exp B)
    · intro n x
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right (hηabs n x) (Real.exp_pos _).le).trans
        (by simpa using hexp x)
    · intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [hηlim x] with n hn
      rw [hn]
  have hintegral : Tendsto
      (fun n => ∫ x : Plane, (Real.exp (F x) ^ 2 * cutoffGradientSq (η n) x) * ‖φ x‖ ^ 2)
      atTop (𝓝 (∫ x : Plane, (Real.exp (F x) ^ 2 * cutoffGradientSq σ x) * ‖φ x‖ ^ 2)) := by
    apply tendsto_integral_mul_sq_norm_of_bounded hφ.2.1
      (a := fun n x => Real.exp (F x) ^ 2 * cutoffGradientSq (η n) x)
      (fun n => ((hF.exp.continuous.pow 2).mul (continuous_cutoffGradientSq (hη n))).measurable)
      (C := Real.exp B ^ 2 * (2 * Cσ + 2 * Cκ))
    · intro n x
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (cutoffGradientSq_nonneg _ _))]
      simpa only [mul_comm] using mul_le_mul (hηgrad n x)
        (pow_le_pow_left₀ (Real.exp_pos _).le (hexp x) 2) (sq_nonneg _)
        (show 0 ≤ 2 * Cσ + 2 * Cκ by positivity)
    · intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [hgradlim x] with n hn
      rw [hn]
  apply le_of_tendsto_of_tendsto (hmass.const_mul δ) (hintegral.const_mul 2)
  exact Filter.Eventually.of_forall fun n =>
    weighted_cutoff_mass_le_gradient_error hV (hη n) (hηc n) hF hφ
      (fun x hx => hreserve x (left_ne_zero_of_mul hx))

end InfiniteZero
