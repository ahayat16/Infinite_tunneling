import InfiniteZero.MagneticInteriorEstimate
import InfiniteZero.WeightedLocalMassComparison
import InfiniteZero.WeightedSemiclassicalJets
import InfiniteZero.CuspPacketNeighborhood
import InfiniteZero.ConstructionSmooth

/-!
# Weighted interior jets for the genuine magnetic equation

On balls of radius `2h`, the Lipschitz weight differs from its central
value by a fixed factor. Removing that weight from the local masses,
applying the proved magnetic rescaling of the classical interior contract,
and restoring the central value gives one inverse-length loss in dimension
two. The weight and the neighborhood indicator are never differentiated.
The classical fixed-ball estimate remains an explicit hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- A fixed constant transports global weighted solution mass and local
weighted data masses to pointwise semiclassical jets on the compact inner
cusp neighborhood. All bounds are uniform in the coupling and center. -/
theorem exists_cusp_weighted_magnetic_interior_jet_bound
    (hInterior : HasInteriorEllipticEstimate) {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p)
    (n : ℕ) (κMax : ℝ) (hκMax : 0 ≤ κMax) :
    ∃ C > 0, ∀ coupling : ℝ, 1 ≤ coupling → ∀ E : ℝ,
      |(coupling⁻¹) ^ 2 * E| ≤ 1 →
      ∀ x₀ ∈ closure p.cuspPacketInnerNeighborhood,
        coupling⁻¹ ≤ p.cuspPacketBallScale →
      ∀ u f : Wavefunction, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
      (∀ x : Plane, (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        (magneticHamiltonian p.b coupling p.potential u x - (E : ℂ) * u x) = f x) →
      ∀ κ ∈ Icc 0 κMax, ∀ U F : ℝ, 0 ≤ U → 0 ≤ F →
      (MemLp (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * u x) 2 volume ∧
        mass (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * u x) ≤ U ^ 2) →
      (∀ j : ℕ, j ≤ n → ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
        MemLp (p.cuspPacketNeighborhood.indicator
          (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) 2 volume ∧
        mass (p.cuspPacketNeighborhood.indicator
          (weightedSemiclassicalJet χ.weight coupling⁻¹ κ f j v)) ≤ F ^ 2) →
      ∀ j : ℕ, j ≤ n →
        Real.exp (κ * coupling * χ.weight x₀) * (coupling⁻¹) ^ j *
          ‖iteratedFDeriv ℝ j u x₀‖ ≤ C * coupling * (U + F) := by
  obtain ⟨Ci, hCi, hinterior⟩ := exists_magnetic_interior_jet_bound
    hInterior p.b p.potential (potential_contDiff hp) n p.cuspPacketRadius 1
  obtain ⟨Cw, hCw, hweight⟩ := χ.exists_local_weight_comparison hκMax
    (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨Ci * Cw, mul_pos hCi hCw, ?_⟩
  intro coupling hc E hE x₀ hx₀ hsmall u f hu hf heq κ hκ U F hU hF huMass hfMass j hj
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hcpos
  have hxRadius : ‖x₀‖ ≤ p.cuspPacketRadius := by
    have hx := closure_cuspPacketInnerNeighborhood_norm_bounds p hx₀
    linarith only [hx.2]
  have hball : Metric.ball x₀ (2 * coupling⁻¹) ⊆ p.cuspPacketNeighborhood :=
    Metric.ball_subset_closedBall.trans (cuspPacket_closedBall_subset hp hx₀ ⟨hh, hsmall⟩)
  let w : Plane → ℝ := fun x => Real.exp (κ * coupling * χ.weight x)
  let w₀ : ℝ := Real.exp (κ * coupling * χ.weight x₀)
  have hw₀ : 0 < w₀ := Real.exp_pos _
  have hw : ∀ x ∈ Metric.ball x₀ (2 * coupling⁻¹),
      0 ≤ w x ∧ w₀ ≤ Cw * w x := by
    intro x hx
    refine ⟨(Real.exp_pos _).le, ?_⟩
    simpa only [w, w₀, div_inv_eq_mul] using
      (hweight coupling⁻¹ hh κ hκ x₀ x (Metric.mem_ball.mp hx).le).1
  have huLocal : (∫ x in Metric.ball x₀ (2 * coupling⁻¹), ‖u x‖ ^ 2) ≤
      (Cw / w₀ * U) ^ 2 := by
    apply setIntegral_norm_sq_le_of_weight_comparison
      (continuous_integrableOn_norm_sq_ball hu.continuous x₀ (2 * coupling⁻¹))
      measurableSet_ball (subset_univ _) hCw.le hw₀ hw
    · simpa only [indicator_univ, w] using huMass.1
    · simpa only [indicator_univ, w] using huMass.2
  have hfLocal : ∀ k : ℕ, k ≤ n → ∀ v : Fin k → Plane, (∀ i, ‖v i‖ ≤ 1) →
      (∫ x in Metric.ball x₀ (2 * coupling⁻¹),
        ‖((coupling⁻¹) ^ k : ℂ) * iteratedFDeriv ℝ k f x v‖ ^ 2) ≤
        (Cw / w₀ * F) ^ 2 := by
    intro k hk v hv
    have hg : Continuous (fun x =>
        ((coupling⁻¹) ^ k : ℂ) * iteratedFDeriv ℝ k f x v) :=
      continuous_const.mul
        (((contDiff_infty.mp hf k).continuous_iteratedFDeriv le_rfl).eval_const v)
    have hweightedJet :
        (fun x => (w x : ℂ) *
          (((coupling⁻¹) ^ k : ℂ) * iteratedFDeriv ℝ k f x v)) =
        weightedSemiclassicalJet χ.weight coupling⁻¹ κ f k v := by
      funext x
      simp only [weightedSemiclassicalJet, w, div_inv_eq_mul]
      ring
    apply setIntegral_norm_sq_le_of_weight_comparison
      (continuous_integrableOn_norm_sq_ball hg x₀ (2 * coupling⁻¹))
      measurableSet_ball hball hCw.le hw₀ hw
    · rw [hweightedJet]
      exact (hfMass k hk v hv).1
    · rw [hweightedJet]
      exact (hfMass k hk v hv).2
  have hjet := hinterior coupling hc E hE x₀ hxRadius u f hu hf heq
    (Cw / w₀ * U) (Cw / w₀ * F)
    (by positivity) (by positivity) huLocal hfLocal j hj
  calc
    _ = w₀ * ((coupling⁻¹) ^ j * ‖iteratedFDeriv ℝ j u x₀‖) := by
      dsimp [w₀]
      ring
    _ ≤ w₀ * (Ci * coupling * (Cw / w₀ * U + Cw / w₀ * F)) :=
      mul_le_mul_of_nonneg_left hjet hw₀.le
    _ = (Ci * Cw) * coupling * (U + F) := by
      field_simp

end InfiniteZero.CuspParameters
