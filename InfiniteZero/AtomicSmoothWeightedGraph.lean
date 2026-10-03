import InfiniteZero.AtomicWeightedTestCoercivity
import InfiniteZero.AtomicSmoothWeight
import InfiniteZero.MagneticWeightedGraph

/-!
# Concrete weighted rank-one coercivity on the full operator graph

The smooth weight is tested on the original test core. Its gradient cost is
absorbed in the exterior IMS reserve. Continuity in the graph coordinates
then proves the inequality on the actual operator domain, without requiring
the weighted vector to belong to that domain.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InfiniteZero.CuspParameters

theorem exists_atomic_smooth_weighted_graph_lower_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ threshold > 0, ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ : Wavefunction, ∃ hφ : IsAtomicGroundState p.b p.core coupling φ,
      IsPositiveRadial φ ∧
      ∀ F : Plane → ℝ, ∀ hF : ContDiff ℝ ∞ F,
      (∀ x, ‖x‖ ≤ 4 * p.r₀ → F x = 0) →
      (∀ x, cutoffGradientSq F x ≤ coupling ^ 2 / 8) →
      ∀ C : ℝ, ∀ hbound : ∀ x, |Real.exp (F x)| ≤ C,
      let W := boundedPotentialMul (fun x => Real.exp (F x)) hF.exp.continuous hbound
      ∀ u : (magneticOperator p.b coupling p.potential).domain,
        (hRad.gap / 2 * coupling) * ‖W (u : L2Space)‖ ^ 2 -
            2 * (hRad.gap * coupling) * ‖inner ℂ (hφ.1.2.1.toLp φ) (W (u : L2Space))‖ ^ 2 ≤
          (inner ℂ (W (u : L2Space)) (W (magneticOperator p.b coupling p.potential u))).re -
            atomicGroundEnergy p.b p.core coupling * ‖W (u : L2Space)‖ ^ 2 := by
  obtain ⟨threshold, hthreshold, htest⟩ :=
    exists_atomic_weighted_test_coercivity_of_radialData hp hRad hAcore
  refine ⟨threshold, hthreshold, ?_⟩
  intro coupling hc
  obtain ⟨φ, hφ, hpos, hcoer⟩ := htest coupling hc
  refine ⟨φ, hφ, hpos, ?_⟩
  intro F hF hzero hgrad C hbound W u
  apply (hApot coupling).weighted_rankOne_lower
    (fun x => Real.exp (F x)) hF.exp.continuous hbound hφ.1.2.1 ?_ u
  intro ψ hψ
  have hpenalty := cutoffGradientSq_le_atomicOuterCutoff_sq hp.r₀_pos
    (div_nonneg (sq_nonneg coupling) (by norm_num)) hzero hgrad
  have h := hcoer (cutoffGradientSq F) (continuous_cutoffGradientSq hF) hpenalty
    (fun x => (Real.exp (F x) : ℂ) * ψ x) (hψ.real_mul hF.exp)
  have he := magneticForm_exp_test p.b coupling (potential_contDiff hp).continuous hF hψ
  linarith only [h, he]

end InfiniteZero.CuspParameters
