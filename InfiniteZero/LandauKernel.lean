import InfiniteZero.BridgeActionMinimum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The real radial proper-time kernel

We define the integral in `eq:K-integral` and prove that it converges and is
strictly positive for positive parameters and radius. Identifying this scalar
integral with an operator resolvent kernel remains a separate obligation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

/-- The positive integrand in the proper-time representation of the radial kernel. -/
def landauIntegrand (b h E r τ : ℝ) : ℝ :=
  (Real.sinh (b * τ))⁻¹ * Real.exp (-properTimePhase b E r τ / h)

/-- The real radial kernel defined by the exact proper-time integral in the blueprint. -/
def landauKernel (b h E r : ℝ) : ℝ :=
  b / (4 * Real.pi * h ^ 2) * ∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ

theorem landauIntegrand_pos {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) (h E r : ℝ) :
    0 < landauIntegrand b h E r τ := by
  unfold landauIntegrand
  have hs : 0 < Real.sinh (b * τ) := Real.sinh_pos_iff.2 (mul_pos hb hτ)
  positivity

theorem continuousOn_landauIntegrand {b : ℝ} (hb : 0 < b) (h E r : ℝ) :
    ContinuousOn (landauIntegrand b h E r) (Ioi 0) := by
  intro τ hτ
  apply ContinuousAt.continuousWithinAt
  unfold landauIntegrand
  have hs : Real.sinh (b * τ) ≠ 0 :=
    (Real.sinh_pos_iff.2 (mul_pos hb hτ)).ne'
  have hx : ContinuousAt (fun t : ℝ => b * t) τ :=
    continuousAt_const.mul continuousAt_id
  have hc : ContinuousAt (fun t : ℝ => (Real.sinh (b * t))⁻¹) τ :=
    (Real.continuous_sinh.continuousAt.comp hx).inv₀ hs
  exact hc.mul (Real.continuous_exp.continuousAt.comp
    ((hasDerivAt_properTimePhase hb hτ E r).continuousAt.neg.div_const h))

private theorem mul_exp_neg_mul_le_inv {c : ℝ} (hc : 0 < c) (y : ℝ) :
    y * Real.exp (-(c * y)) ≤ c⁻¹ := by
  have hexp : c * y * Real.exp (-(c * y)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (c * y)).trans (by
      rw [Real.exp_le_one_iff]
      norm_num)
  rw [inv_eq_one_div, le_div_iff₀ hc]
  nlinarith only [hexp]

/-- A single exponential bound controls both the singular endpoint and the infinite tail. -/
theorem landauIntegrand_le_exp {b h r τ : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hr : 0 < r) (hτ : 0 < τ) (E : ℝ) :
    landauIntegrand b h E r τ ≤
      (4 * h / (b * r ^ 2)) * Real.exp ((-E / h) * τ) := by
  let c := b * r ^ 2 / (4 * h)
  let y := (Real.sinh (b * τ))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hy : 0 < y := by
    dsimp [y]
    exact inv_pos.2 (Real.sinh_pos_iff.2 (mul_pos hb hτ))
  have hcosh := Real.one_le_cosh (b * τ)
  have hfactor : landauIntegrand b h E r τ =
      (y * Real.exp (-(c * Real.cosh (b * τ) * y))) * Real.exp ((-E / h) * τ) := by
    unfold landauIntegrand properTimePhase
    dsimp [c, y]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hsmall : y * Real.exp (-(c * Real.cosh (b * τ) * y)) ≤ c⁻¹ := by
    calc
      y * Real.exp (-(c * Real.cosh (b * τ) * y)) ≤
          y * Real.exp (-(c * y)) := by
        apply mul_le_mul_of_nonneg_left _ hy.le
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (mul_pos hc hy).le (sub_nonneg.mpr hcosh)]
      _ ≤ c⁻¹ := mul_exp_neg_mul_le_inv hc y
  rw [hfactor]
  have hcInv : c⁻¹ = 4 * h / (b * r ^ 2) := by
    dsimp [c]
    rw [inv_div]
  rw [← hcInv]
  exact mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le

theorem integrableOn_landauIntegrand {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    IntegrableOn (landauIntegrand b h E r) (Ioi 0) := by
  have hexp := (integrableOn_exp_mul_Ioi
    (div_neg_of_neg_of_pos (neg_neg_of_pos hE) hh) 0).const_mul
    (4 * h / (b * r ^ 2))
  apply hexp.mono' ((continuousOn_landauIntegrand hb h E r).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [Real.norm_eq_abs, abs_of_pos (landauIntegrand_pos hb hτ h E r)]
  exact landauIntegrand_le_exp hb hh hr hτ E

theorem integral_landauIntegrand_pos {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    0 < ∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] landauIntegrand b h E r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact (landauIntegrand_pos hb hτ h E r).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn
    (integrableOn_landauIntegrand hb hh hE hr)).2
  have hs : Function.support (landauIntegrand b h E r) ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro τ hτ
    exact (landauIntegrand_pos hb hτ h E r).ne'
  rw [hs, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

theorem landauKernel_pos {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    0 < landauKernel b h E r := by
  unfold landauKernel
  exact mul_pos (by positivity) (integral_landauIntegrand_pos hb hh hE hr)

theorem integral_landauIntegrand_le {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    (∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ) ≤
      (4 * h / (b * r ^ 2)) * (h / E) := by
  have hneg : -E / h < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hE) hh
  have hexp := (integrableOn_exp_mul_Ioi hneg 0).const_mul (4 * h / (b * r ^ 2))
  calc
    (∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ) ≤
        ∫ τ in Ioi (0 : ℝ), (4 * h / (b * r ^ 2)) * Real.exp ((-E / h) * τ) := by
      apply integral_mono_ae (integrableOn_landauIntegrand hb hh hE hr) hexp
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      exact landauIntegrand_le_exp hb hh hr hτ E
    _ = (4 * h / (b * r ^ 2)) * (h / E) := by
      rw [integral_const_mul, integral_exp_mul_Ioi hneg]
      simp only [mul_zero, Real.exp_zero]
      field_simp

/-- A finite upper bound independent of the semiclassical parameter. -/
theorem landauKernel_le {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    landauKernel b h E r ≤ 1 / (Real.pi * E * r ^ 2) := by
  have hbound := mul_le_mul_of_nonneg_left (integral_landauIntegrand_le hb hh hE hr)
    (show 0 ≤ b / (4 * Real.pi * h ^ 2) by positivity)
  unfold landauKernel
  convert hbound using 1
  field_simp

end InfiniteZero
