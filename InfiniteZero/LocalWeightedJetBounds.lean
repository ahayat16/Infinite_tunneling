import InfiniteZero.WeightedSemiclassicalJets
import InfiniteZero.LocalCompactL2Bound
import InfiniteZero.GenericFiniteL2Bound

/-!
# Local L² bounds for weighted semiclassical jets

A bound on the multilinear jet over a bounded measurable region controls
each unit-direction evaluation in the genuine local L² space. The weight
and the indicator are applied after differentiation. Finite families may
use different derivative orders and directions while retaining one common
pointwise bound and the exact area factor of the fixed planar ball.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- A local operator-norm bound gives integrability and the squared L²
bound for the actual weighted directional jet restricted to the region. -/
theorem memLp_mass_indicator_weightedSemiclassicalJet
    {T : Plane → ℝ} (hT : Continuous T) {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    {s : Set Plane} {R B h κ : ℝ} (hs : MeasurableSet s) (hR : 0 ≤ R)
    (hsR : s ⊆ Metric.closedBall (0 : Plane) R) (hh : 0 ≤ h) (hB : 0 ≤ B)
    (n : ℕ) (v : Fin n → Plane) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hbound : ∀ x ∈ s,
      Real.exp (κ / h * T x) * h ^ n * ‖iteratedFDeriv ℝ n u x‖ ≤ B) :
    MemLp (s.indicator (weightedSemiclassicalJet T h κ u n v)) 2 volume ∧
      mass (s.indicator (weightedSemiclassicalJet T h κ u n v)) ≤
        (Real.sqrt Real.pi * R * B) ^ 2 := by
  have hF : AEStronglyMeasurable (weightedSemiclassicalJet T h κ u n v) volume :=
    (weightedSemiclassicalJet_continuous hT h κ hu n v).aestronglyMeasurable
  have hpoint (x : Plane) (hx : x ∈ s) :
      ‖weightedSemiclassicalJet T h κ u n v x‖ ≤ B :=
    (norm_weightedSemiclassicalJet_le T hh κ u n v hv x).trans (hbound x hx)
  exact ⟨memLp_indicator_of_bound_on_subset_closedBall hF hs hsR hB hpoint,
    mass_indicator_le_pi_mul_radius_sq_mul_bound_sq hF hs hR hsR hB hpoint⟩

/-- The same local mass bound written as the actual integral over the
region. This neither differentiates the indicator nor imposes its smoothness. -/
theorem setIntegral_norm_sq_weightedSemiclassicalJet_le
    {T : Plane → ℝ} (hT : Continuous T) {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    {s : Set Plane} {R B h κ : ℝ} (hs : MeasurableSet s) (hR : 0 ≤ R)
    (hsR : s ⊆ Metric.closedBall (0 : Plane) R) (hh : 0 ≤ h) (hB : 0 ≤ B)
    (n : ℕ) (v : Fin n → Plane) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hbound : ∀ x ∈ s,
      Real.exp (κ / h * T x) * h ^ n * ‖iteratedFDeriv ℝ n u x‖ ≤ B) :
    (∫ x in s, ‖weightedSemiclassicalJet T h κ u n v x‖ ^ 2) ≤
      (Real.sqrt Real.pi * R * B) ^ 2 := by
  rw [← mass_indicator_eq_setIntegral s hs]
  exact (memLp_mass_indicator_weightedSemiclassicalJet
    hT hu hs hR hsR hh hB n v hv hbound).2

/-- A common bound through order `n` controls any finite family of local
Hilbert L² norms. The cardinality is kept explicit; repeated directions or
orders are allowed, and every term belongs to the same wavefunction. -/
theorem exists_memLp_sum_norm_indicator_weightedSemiclassicalJet_le
    {T : Plane → ℝ} (hT : Continuous T) {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    {s : Set Plane} {R B h κ : ℝ} (hs : MeasurableSet s) (hR : 0 ≤ R)
    (hsR : s ⊆ Metric.closedBall (0 : Plane) R) (hh : 0 ≤ h) (hB : 0 ≤ B)
    (n : ℕ)
    (hbound : ∀ j : ℕ, j ≤ n → ∀ x ∈ s,
      Real.exp (κ / h * T x) * h ^ j * ‖iteratedFDeriv ℝ j u x‖ ≤ B)
    {ι : Type*} [Fintype ι] (orders : ι → ℕ) (horders : ∀ i, orders i ≤ n)
    (v : (i : ι) → Fin (orders i) → Plane) (hv : ∀ i j, ‖v i j‖ ≤ 1) :
    ∃ hF : ∀ i, MemLp
        (s.indicator (weightedSemiclassicalJet T h κ u (orders i) (v i))) 2 volume,
      (∑ i, ‖(hF i).toLp
        (s.indicator (weightedSemiclassicalJet T h κ u (orders i) (v i)))‖) ≤
          (Fintype.card ι : ℝ) * Real.sqrt Real.pi * R * B := by
  have hi (i : ι) := memLp_mass_indicator_weightedSemiclassicalJet
    hT hu hs hR hsR hh hB (orders i) (v i) (hv i) (hbound (orders i) (horders i))
  refine ⟨fun i => (hi i).1, ?_⟩
  calc
    _ ≤ (Fintype.card ι : ℝ) * (Real.sqrt Real.pi * R * B) :=
      sum_norm_toLp_le_card_mul_of_mass_le_sq
        (fun i => s.indicator (weightedSemiclassicalJet T h κ u (orders i) (v i)))
        (fun i => (hi i).1) (by positivity) (fun i => (hi i).2)
    _ = _ := by ring

end InfiniteZero
