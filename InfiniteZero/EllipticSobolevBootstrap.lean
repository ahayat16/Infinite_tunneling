import InfiniteZero.EllipticSourceSobolev

/-!
# Finite-order uniform elliptic bootstrap

The base estimate and the product bounds are combined on finitely many
nested balls. All constants are chosen before the coefficients and the
solution, so uniformity in their prescribed derivative bounds is part of
the conclusion of the proof.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- A uniform local estimate at order zero implies all finite-order
estimates. Each induction step uses two fixed nested pairs of balls. -/
theorem localCoordinateEllipticEstimate_of_zero
    (hzero : HasLocalCoordinateEllipticEstimate 0) (n : ℕ) :
    HasLocalCoordinateEllipticEstimate n := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    intro r R hr hrR B hB
    let s := (r + R) / 2
    have hrs : r < s := by dsimp [s]; linarith
    have hsR : s < R := by dsimp [s]; linarith
    have hs : 0 < s := hr.trans hrs
    obtain ⟨C₀, hC₀, houter⟩ := ih s R hs hsR B hB
    obtain ⟨C₁, hC₁, hinner⟩ := ih r s hr hrs B hB
    obtain ⟨D, hD, hsource⟩ := ellipticDerivativeSource_sobolev_bound n hB
    refine ⟨1 + 2 * C₁ * (C₀ + D * (1 + C₀)), by positivity, ?_⟩
    intro a q u f ha hq hu hf hcoeff heq
    let W := coordinateSobolevNorm 0 R u + coordinateSobolevNorm (n + 1) R f
    have hW : 0 ≤ W := add_nonneg (coordinateSobolevNorm_nonneg _ _ _)
      (coordinateSobolevNorm_nonneg _ _ _)
    have huR : coordinateSobolevNorm 0 R u ≤ W :=
      le_add_of_nonneg_right (coordinateSobolevNorm_nonneg _ _ _)
    have hfR : coordinateSobolevNorm (n + 1) R f ≤ W :=
      le_add_of_nonneg_left (coordinateSobolevNorm_nonneg _ _ _)
    have hlower : coordinateSobolevNorm (n + 2) s u ≤ C₀ * W := by
      calc
        _ ≤ C₀ * (coordinateSobolevNorm 0 R u + coordinateSobolevNorm n R f) :=
          houter a q u f ha hq hu hf (hcoeff.mono_order (Nat.le_succ n)) heq
        _ ≤ C₀ * W := mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (coordinateSobolevNorm_mono_order (Nat.le_succ n) R f))
          hC₀.le
    have huS : coordinateSobolevNorm (n + 1) s u ≤ C₀ * W :=
      (coordinateSobolevNorm_mono_order (by omega) s u).trans hlower
    have hfS : coordinateSobolevNorm (n + 1) s f ≤ W :=
      (coordinateSobolevNorm_mono_radius hf (n + 1) hsR.le).trans hfR
    have hcoeffS := hcoeff.mono_radius hsR.le
    have hnewSource (i : Fin 2) :
        coordinateSobolevNorm n s (ellipticDerivativeSource i a q u f) ≤
          (D * (1 + C₀)) * W := by
      calc
        _ ≤ D * (coordinateSobolevNorm (n + 1) s f +
              coordinateSobolevNorm (n + 1) s u) :=
          hsource s a q u f ha hq hu hf hcoeffS i
        _ ≤ D * (W + C₀ * W) :=
          mul_le_mul_of_nonneg_left (add_le_add hfS huS) hD.le
        _ = _ := by ring
    have hderivMass (i : Fin 2) :
        coordinateSobolevNorm 0 s (partialDerivative i u) ≤ C₀ * W :=
      (coordinateSobolevNorm_partialDerivative_le hu 0 s i).trans
        ((coordinateSobolevNorm_mono_order (by omega) s u).trans hlower)
    have hhigher (i : Fin 2) :
        coordinateSobolevNorm (n + 2) r (partialDerivative i u) ≤
          (C₁ * (C₀ + D * (1 + C₀))) * W := by
      have hlocal := hinner a q (partialDerivative i u)
        (ellipticDerivativeSource i a q u f) ha hq (contDiff_partialDerivative i hu)
        (contDiff_ellipticDerivativeSource i ha hq hu hf)
        (hcoeffS.mono_order (Nat.le_succ n))
        (ellipticExpression_partialDerivative_on_ball i ha hq hu
          (fun x hx => heq x (Metric.ball_subset_ball hsR.le hx)))
      calc
        _ ≤ C₁ * (coordinateSobolevNorm 0 s (partialDerivative i u) +
          coordinateSobolevNorm n s (ellipticDerivativeSource i a q u f)) := hlocal
        _ ≤ C₁ * (C₀ * W + (D * (1 + C₀)) * W) :=
          mul_le_mul_of_nonneg_left (add_le_add (hderivMass i) (hnewSource i)) hC₁.le
        _ = _ := by ring
    have huInner : coordinateSobolevNorm 0 r u ≤ W :=
      (coordinateSobolevNorm_mono_radius hu 0 hrR.le).trans huR
    have hrec := coordinateSobolevNorm_succ_le hu (n + 2) r
    simp only [Fin.sum_univ_two] at hrec
    change coordinateSobolevNorm ((n + 2) + 1) r u ≤
      (1 + 2 * C₁ * (C₀ + D * (1 + C₀))) * W
    nlinarith [hhigher 0, hhigher 1]

/-- Specialization to the fixed balls used by the public elliptic contract. -/
theorem coordinateInteriorSobolevEstimate_of_local_zero
    (hzero : HasLocalCoordinateEllipticEstimate 0) : HasCoordinateInteriorSobolevEstimate := by
  intro n B hB
  obtain ⟨C, hC, hc⟩ := localCoordinateEllipticEstimate_of_zero hzero n
    1 2 (by norm_num) (by norm_num) B hB
  refine ⟨C, hC, ?_⟩
  intro a q u f ha hq hu hf hcoeff heq
  simpa only [coordinateSobolevNorm_zero] using hc a q u f ha hq hu hf hcoeff heq

end InfiniteZero
