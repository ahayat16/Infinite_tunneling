import InfiniteZero.CuspWeight

/-!
# Local oscillation of a Lipschitz exponential weight

On balls of radius proportional to `h`, the ratio of exponential weights
is bounded independently of `h`. This is the weight comparison needed for
interior estimates after rescaling; no derivative of the weight is taken.
-/

noncomputable section
open Set
open scoped NNReal

namespace InfiniteZero

theorem exponentialWeight_ratio_bounds {T : Plane → ℝ} {K : ℝ≥0}
    (hT : LipschitzWith K T) {h κ ρ : ℝ} (hh : 0 < h) (hκ : 0 ≤ κ)
    {x x₀ : Plane} (hx : dist x x₀ ≤ ρ * h) :
    Real.exp (κ / h * T x) / Real.exp (κ / h * T x₀) ∈
      Icc (Real.exp (-(κ * K * ρ))) (Real.exp (κ * K * ρ)) := by
  have hdelta : |T x - T x₀| ≤ (K : ℝ) * (ρ * h) := by
    simpa only [Real.dist_eq] using hT.dist_le_mul_of_le hx
  have hscaled : |κ / h * (T x - T x₀)| ≤ κ * K * ρ := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hκ hh.le)]
    calc
      _ ≤ κ / h * ((K : ℝ) * (ρ * h)) :=
        mul_le_mul_of_nonneg_left hdelta (div_nonneg hκ hh.le)
      _ = _ := by field_simp
  rw [← Real.exp_sub]
  have heq : κ / h * T x - κ / h * T x₀ = κ / h * (T x - T x₀) := by ring
  rw [heq]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hscaled).1,
    Real.exp_le_exp.mpr (abs_le.mp hscaled).2⟩

namespace CuspParameters.CuspWeightCutoffs

/-- For the actual cusp weight, one constant works for every center, positive
scale and weight strength in a fixed compact nonnegative interval. -/
theorem exists_local_weight_comparison {p : CuspParameters} (χ : CuspWeightCutoffs p)
    {κMax ρ : ℝ} (_hκMax : 0 ≤ κMax) (hρ : 0 ≤ ρ) :
    ∃ C > 0, ∀ h : ℝ, 0 < h → ∀ κ ∈ Icc (0 : ℝ) κMax,
      ∀ x₀ x : Plane, dist x x₀ ≤ ρ * h →
      Real.exp (κ / h * χ.weight x₀) ≤ C * Real.exp (κ / h * χ.weight x) ∧
      Real.exp (κ / h * χ.weight x) ≤ C * Real.exp (κ / h * χ.weight x₀) := by
  obtain ⟨K, hK⟩ := χ.weight_lipschitz
  refine ⟨Real.exp (κMax * K * ρ), Real.exp_pos _, ?_⟩
  intro h hh κ hκ x₀ x hx
  have hC : Real.exp (κ * K * ρ) ≤ Real.exp (κMax * K * ρ) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hκ.2 K.coe_nonneg) hρ
  have hforward := (exponentialWeight_ratio_bounds hK hh hκ.1 hx).2.trans hC
  have hreverse := (exponentialWeight_ratio_bounds hK hh hκ.1
    (show dist x₀ x ≤ ρ * h by simpa only [dist_comm] using hx)).2.trans hC
  exact ⟨(div_le_iff₀ (Real.exp_pos _)).mp hreverse,
    (div_le_iff₀ (Real.exp_pos _)).mp hforward⟩

end CuspParameters.CuspWeightCutoffs
end InfiniteZero
