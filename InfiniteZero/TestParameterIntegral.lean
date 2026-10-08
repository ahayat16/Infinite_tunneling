import InfiniteZero.MagneticModel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating parameter integrals against test functions

Compact support of the test function turns joint continuity of the
parameter derivative into a local integrable bound.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InfiniteZero

/-- Parameter differentiation under a spatial test integral, with a
jointly continuous derivative on positive times. -/
theorem hasDerivAt_integral_mul_test {F F' : ℝ → Plane → ℂ}
    (hF : ∀ s : ℝ, 0 < s → Continuous (F s))
    (hF' : ContinuousOn (fun p : ℝ × Plane => F' p.1 p.2) (Ioi 0 ×ˢ univ))
    (hd : ∀ s : ℝ, 0 < s → ∀ y : Plane,
      HasDerivAt (fun t => F t y) (F' s y) s)
    {f : Wavefunction} (hf : IsTestFunction f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ y : Plane, F s y * f y)
      (∫ y : Plane, F' t y * f y) t := by
  let K : Set (ℝ × Plane) := Icc (t / 2) (2 * t) ×ˢ tsupport f
  have hK : IsCompact K := isCompact_Icc.prod hf.2
  have hKsub : K ⊆ Ioi 0 ×ˢ univ := by
    intro p hp
    exact ⟨(half_pos ht).trans_le hp.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKsub)
  have hF't : Continuous (F' t) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hp : (t, y) ∈ Ioi 0 ×ˢ (univ : Set Plane) := ⟨ht, mem_univ y⟩
    exact (hF'.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)).comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hint : Integrable (fun y : Plane => F t y * f y) :=
    ((hF t ht).mul hf.1.continuous).integrable_of_hasCompactSupport hf.2.mul_left
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => F s y * f y) (F' := fun s y => F' s y * f y)
    (s := Icc (t / 2) (2 * t)) (bound := fun y => max M 0 * ‖f y‖)
    (Icc_mem_nhds (by linarith) (by linarith))
    (by filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ((hF s hs).mul hf.1.continuous).aestronglyMeasurable)
    hint ((hF't.mul hf.1.continuous).aestronglyMeasurable) ?_ ?_ ?_
  · exact hderiv.2
  · filter_upwards with y s hs
    by_cases hy : y ∈ tsupport f
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((hM (s, y) ⟨hs, hy⟩).trans (le_max_left _ _)) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hf.1.continuous.integrable_of_hasCompactSupport hf.2).norm.const_mul _
  · filter_upwards with y s hs
    exact (hd s ((half_pos ht).trans_le hs.1) y).mul_const _

end InfiniteZero
