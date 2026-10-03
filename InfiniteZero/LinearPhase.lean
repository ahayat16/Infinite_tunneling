import InfiniteZero.SpectralAssembly
import Mathlib.Topology.Algebra.Order.Field

/-!
# Positive linear phase growth implies oscillation

The geometric coefficient enters through the limit `phase x / x → slope`.
Its positivity supplies divergence of the phase; divergence is not requested
as a second independent analytic hypothesis.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace InfiniteZero

/-- A positive asymptotic linear slope forces a real phase to diverge. -/
theorem tendsto_atTop_of_phase_ratio {phase : ℝ → ℝ} {slope : ℝ}
    (hRatio : Tendsto (fun x => phase x / x) atTop (𝓝 slope)) (hSlope : 0 < slope) :
    Tendsto phase atTop atTop := by
  have hmul : Tendsto (fun x : ℝ => x * (phase x / x)) atTop atTop :=
    Tendsto.atTop_mul_pos hSlope tendsto_id hRatio
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [ne_of_gt hx]

/-- Cosine asymptotics with a specified leading linear phase coefficient. -/
structure LinearCosineAsymptotic (f : ℝ → ℝ) (slope : ℝ) where
  threshold : ℝ
  amplitude : ℝ → ℝ
  phase : ℝ → ℝ
  error : ℝ → ℝ
  amplitude_pos : ∀ x, threshold ≤ x → 0 < amplitude x
  phase_continuous : ContinuousOn phase (Ici threshold)
  phase_ratio : Tendsto (fun x => phase x / x) atTop (𝓝 slope)
  error_tendsto : Tendsto error atTop (𝓝 0)
  formula : ∀ x, threshold ≤ x →
    f x = amplitude x * (Real.cos (phase x) + error x)

/-- The positivity proof may come from the explicit geometric certificate. -/
def LinearCosineAsymptotic.toCosineAsymptotic {f : ℝ → ℝ} {slope : ℝ}
    (h : LinearCosineAsymptotic f slope) (hSlope : 0 < slope) : CosineAsymptotic f where
  threshold := h.threshold
  amplitude := h.amplitude
  phase := h.phase
  error := h.error
  amplitude_pos := h.amplitude_pos
  phase_continuous := h.phase_continuous
  phase_tendsto := tendsto_atTop_of_phase_ratio h.phase_ratio hSlope
  error_tendsto := h.error_tendsto
  formula := h.formula

/-- Analytic spectral data exposing the actual leading phase coefficient. -/
structure LinearSpectralAsymptotics (Ee Eo rho : ℝ → ℝ) (slope : ℝ) where
  hopping : LinearCosineAsymptotic (fun x => -rho x) slope
  transfer : Tendsto
    (fun x => (Eo x - Ee x + 2 * rho x) / (2 * hopping.amplitude x)) atTop (𝓝 0)
  threshold : ℝ
  splitting_continuous : ContinuousOn (fun x => Eo x - Ee x) (Ici threshold)
  hopping_continuous : ContinuousOn rho (Ici threshold)

/-- The existing zero and parity assembly applies after the slope is shown positive. -/
def LinearSpectralAsymptotics.toSpectralAsymptotics {Ee Eo rho : ℝ → ℝ} {slope : ℝ}
    (h : LinearSpectralAsymptotics Ee Eo rho slope) (hSlope : 0 < slope) :
    SpectralAsymptotics Ee Eo rho where
  hopping := h.hopping.toCosineAsymptotic hSlope
  transfer := h.transfer
  threshold := h.threshold
  splitting_continuous := h.splitting_continuous
  hopping_continuous := h.hopping_continuous

end InfiniteZero
