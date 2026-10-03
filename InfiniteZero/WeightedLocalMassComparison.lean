import InfiniteZero.LocalCompactL2Bound
import InfiniteZero.LipschitzExponentialWeightLocal
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Removing a locally comparable positive weight from a local mass

The weighted function can be known in L² only after restriction to a larger
set. The weight is never differentiated. This supplies the norm transport
needed on a ball of semiclassical radius.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

theorem continuous_integrableOn_norm_sq_ball {u : Wavefunction}
    (hu : Continuous u) (x₀ : Plane) (r : ℝ) :
    IntegrableOn (fun x => ‖u x‖ ^ 2) (Metric.ball x₀ r) volume := by
  exact ((hu.norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall x₀ r)).mono_set Metric.ball_subset_closedBall

theorem setIntegral_norm_sq_le_of_weight_comparison
    {u : Wavefunction} {w : Plane → ℝ} {s t : Set Plane} {C w₀ B : ℝ}
    (hu : IntegrableOn (fun x => ‖u x‖ ^ 2) s volume)
    (hs : MeasurableSet s) (hst : s ⊆ t) (_hC : 0 ≤ C) (hw₀ : 0 < w₀)
    (hw : ∀ x ∈ s, 0 ≤ w x ∧ w₀ ≤ C * w x)
    (hF : MemLp (t.indicator (fun x => (w x : ℂ) * u x)) 2 volume)
    (hbound : mass (t.indicator (fun x => (w x : ℂ) * u x)) ≤ B ^ 2) :
    (∫ x in s, ‖u x‖ ^ 2) ≤ (C / w₀ * B) ^ 2 := by
  let F : Wavefunction := t.indicator (fun x => (w x : ℂ) * u x)
  have hFi : Integrable (fun x => ‖F x‖ ^ 2) volume := hF.norm.integrable_sq
  have hpoint (x : Plane) (hx : x ∈ s) : ‖u x‖ ≤ C / w₀ * ‖F x‖ := by
    have hxw := hw x hx
    have hmul := mul_le_mul_of_nonneg_right hxw.2 (norm_nonneg (u x))
    have hFnorm : ‖F x‖ = w x * ‖u x‖ := by
      simp only [F, indicator_of_mem (hst hx), norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hxw.1]
    rw [hFnorm]
    calc
      _ ≤ (C * w x * ‖u x‖) / w₀ :=
        (le_div_iff₀ hw₀).mpr (by simpa only [mul_comm ‖u x‖ w₀] using hmul)
      _ = _ := by ring
  have hpointSq (x : Plane) (hx : x ∈ s) :
      ‖u x‖ ^ 2 ≤ (C / w₀) ^ 2 * ‖F x‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hpoint x hx) 2
  calc
    _ ≤ ∫ x in s, (C / w₀) ^ 2 * ‖F x‖ ^ 2 :=
      setIntegral_mono_on hu (hFi.const_mul _).integrableOn hs hpointSq
    _ = (C / w₀) ^ 2 * ∫ x in s, ‖F x‖ ^ 2 := integral_const_mul _ _
    _ ≤ (C / w₀) ^ 2 * mass F := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact setIntegral_le_integral hFi (Filter.Eventually.of_forall fun x => sq_nonneg _)
    _ ≤ (C / w₀) ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = _ := by ring

end InfiniteZero
