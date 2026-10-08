import InfiniteZero.EllipticSobolevContract
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# From classical Sobolev estimates to the directional-jet contract

The two Sobolev estimates are explicit hypotheses. This file proves all
finite-dimensional norm comparisons and the choice of a constant uniform
in the derivative order `j ≤ n`. It contains no classical admission.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- Interior Sobolev regularity and Sobolev embedding imply the contract
used by the magnetic rescaling proofs. The chosen constant absorbs the
number of coordinate derivatives and the tensor norm comparison. -/
theorem interiorEllipticEstimate_of_sobolev_estimates
    (hInterior : HasCoordinateInteriorSobolevEstimate)
    (hEmbedding : HasCoordinateSobolevEmbedding) : HasInteriorEllipticEstimate := by
  intro n B hB
  obtain ⟨Ci, hCi, hi⟩ := hInterior n B hB
  obtain ⟨Cs, hCs, hs⟩ := hEmbedding n
  refine ⟨2 ^ n * Cs * Ci * (1 + Real.sqrt (coordinateJetCount n)), by positivity, ?_⟩
  intro a q u f ha hq hu hf hcoeff heq U F hU hF hmass hsource j hj
  have hcoordinate : ∀ k : ℕ, k ≤ n → ∀ x ∈ Metric.ball (0 : Plane) 2,
      ∀ α : Fin k → Fin 2,
        (∀ i, ‖iteratedFDeriv ℝ k (a i) x (fun l => coordinateVector (α l))‖ ≤ B) ∧
        ‖iteratedFDeriv ℝ k q x (fun l => coordinateVector (α l))‖ ≤ B := by
    intro k hk x hx α
    exact ⟨fun i => (coordinate_tensor_component_le _ α).trans ((hcoeff k hk x hx).1 i),
      (coordinate_tensor_component_le _ α).trans (hcoeff k hk x hx).2⟩
  have hlocal := hi a q u f ha hq hu hf hcoordinate heq
  have hmass' : Real.sqrt (∫ x in Metric.ball (0 : Plane) 2, ‖u x‖ ^ 2) ≤ U :=
    Real.sqrt_le_iff.mpr ⟨hU, hmass⟩
  have hsource' := coordinateSobolevNorm_le_of_directional_bounds n 2 f hF hsource
  have hdata : Real.sqrt (∫ x in Metric.ball (0 : Plane) 2, ‖u x‖ ^ 2) +
      coordinateSobolevNorm n 2 f ≤
      (1 + Real.sqrt (coordinateJetCount n)) * (U + F) := by
    calc
      _ ≤ U + Real.sqrt (coordinateJetCount n) * F := add_le_add hmass' hsource'
      _ ≤ _ := by nlinarith [Real.sqrt_nonneg (coordinateJetCount n)]
  calc
    ‖iteratedFDeriv ℝ j u 0‖ ≤ 2 ^ j * (Cs * coordinateSobolevNorm (n + 2) 1 u) :=
      tensor_norm_le_of_coordinate_bound _ (hs u hu j hj)
    _ ≤ 2 ^ n * (Cs * (Ci *
        ((1 + Real.sqrt (coordinateJetCount n)) * (U + F)))) := by
      have hpower : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
      exact mul_le_mul hpower
        (mul_le_mul_of_nonneg_left
          (hlocal.trans (mul_le_mul_of_nonneg_left hdata hCi.le)) hCs.le)
        (mul_nonneg hCs.le (coordinateSobolevNorm_nonneg _ _ _)) (by positivity)
    _ = _ := by ring

end InfiniteZero
