import InfiniteZero.LinearPhase
import InfiniteZero.MagneticModel
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Envelope-relative transfer from exact parity Schur equations

The scalar transfer estimate is derived from the exact Rayleigh quotients,
vanishing overlap, the diagonal defect estimate and the two self-energy
estimates. The error is normalized by a positive envelope, including where
the hopping itself vanishes. The analytic estimates remain explicit inputs.
-/

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace InfiniteZero

theorem rayleigh_difference (E δ ρ s : ℝ) (hs : s ^ 2 ≠ 1) :
    (E + (δ - ρ) / (1 - s)) - (E + (δ + ρ) / (1 + s)) =
      -2 * ρ + (2 * δ * s - 2 * ρ * s ^ 2) / (1 - s ^ 2) := by
  have hm : 1 - s ≠ 0 := by
    intro hz
    apply hs
    have : s = 1 := by linarith
    simp [this]
  have hp : 1 + s ≠ 0 := by
    intro hz
    apply hs
    have : s = -1 := by linarith
    simp [this]
  have hsq : 1 - s ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  field_simp
  ring

theorem LinearCosineAsymptotic.isBigO_amplitude {f : ℝ → ℝ} {slope : ℝ}
    (h : LinearCosineAsymptotic f slope) : f =O[atTop] h.amplitude := by
  apply IsBigO.of_bound 2
  have he : ∀ᶠ x in atTop, |h.error x| < 1 := by
    have ht := h.error_tendsto.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  filter_upwards [eventually_ge_atTop h.threshold, he] with x hx hex
  rw [h.formula x hx, norm_mul]
  have hb : ‖Real.cos (h.phase x) + h.error x‖ ≤ 2 := by
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (by linarith [Real.abs_cos_le_one (h.phase x)])
  nlinarith [norm_nonneg (h.amplitude x)]

/-- The real-variable part of T8.5, derived from the component estimates. -/
theorem parity_schur_transfer
    {Ee Eo base ρ δ s sigmaE sigmaO A : ℝ → ℝ}
    (hA : ∀ᶠ x in atTop, A x ≠ 0)
    (he : ∀ᶠ x in atTop, Ee x = base x + (δ x + ρ x) / (1 + s x) - sigmaE x)
    (ho : ∀ᶠ x in atTop, Eo x = base x + (δ x - ρ x) / (1 - s x) - sigmaO x)
    (hs : Tendsto s atTop (𝓝 0))
    (hρ : ρ =O[atTop] A) (hδ : δ =o[atTop] A)
    (hSigmaE : sigmaE =o[atTop] A) (hSigmaO : sigmaO =o[atTop] A) :
    Tendsto (fun x => (Eo x - Ee x + 2 * ρ x) / (2 * A x)) atTop (𝓝 0) := by
  have hsO : s =o[atTop] (fun _ : ℝ => (1 : ℝ)) := (isLittleO_one_iff ℝ).mpr hs
  have hs2 : Tendsto (fun x => s x ^ 2) atTop (𝓝 0) := by simpa using hs.pow 2
  have hs2O : (fun x => s x ^ 2) =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr hs2
  have hd : Tendsto (fun x => δ x * s x / A x) atTop (𝓝 0) := by
    simpa only [mul_one] using (hδ.mul_isBigO hsO.isBigO).tendsto_div_nhds_zero
  have hr : Tendsto (fun x => ρ x * s x ^ 2 / A x) atTop (𝓝 0) := by
    simpa only [mul_one] using (hρ.mul_isLittleO hs2O).tendsto_div_nhds_zero
  have hden : Tendsto (fun x => 1 - s x ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hs2
  have hlim := ((hd.sub hr).div hden (by norm_num : (1 : ℝ) ≠ 0)).add
    ((hSigmaE.tendsto_div_nhds_zero.sub hSigmaO.tendsto_div_nhds_zero).div_const 2)
  simp only [sub_zero, zero_div, zero_add] at hlim
  apply hlim.congr'
  have hsq : ∀ᶠ x in atTop, s x ^ 2 ≠ 1 :=
    (hs2.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hx => ne_of_lt hx)
  filter_upwards [hA, he, ho, hsq] with x hAx hex hox hsx
  rw [hex, hox]
  simp only [Pi.div_apply]
  have hm : 1 - s x ≠ 0 := by
    intro hz
    apply hsx
    have : s x = 1 := by linarith
    simp [this]
  have hp : 1 + s x ≠ 0 := by
    intro hz
    apply hsx
    have : s x = -1 := by linarith
    simp [this]
  have hsq' : 1 - s x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hsx)
  field_simp
  ring

/-- Real overlap of the canonical translated atomic states. -/
def canonicalOverlap (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  (waveInner (leftState b L coupling (canonicalAtomicState b v coupling))
    (rightState b L coupling (canonicalAtomicState b v coupling))).re

/-- The unscaled diagonal defect, with the opposite-well potential. -/
def canonicalDefect (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  coupling ^ 2 * ∫ x : Plane, v (-x + displacement L) *
    ‖leftState b L coupling (canonicalAtomicState b v coupling) x‖ ^ 2

/-- The precise spectral data for the transfer step. The overlap, defect,
hopping and sector energies are fixed physical quantities. Their construction,
including both self-energy corrections and their relative smallness, is
proved in `CanonicalParityRelativeErrors`. -/
structure CanonicalParitySchurData (b : ℝ) (v : Potential) (L : ℝ) (A : ℝ → ℝ) where
  threshold : ℝ
  sigmaEven : ℝ → ℝ
  sigmaOdd : ℝ → ℝ
  even_equation : ∀ x, threshold ≤ x → evenEnergy b v L x =
    atomicGroundEnergy b v x +
      (canonicalDefect b v L x + (canonicalHopping b v L x).re) /
        (1 + canonicalOverlap b v L x) - sigmaEven x
  odd_equation : ∀ x, threshold ≤ x → oddEnergy b v L x =
    atomicGroundEnergy b v x +
      (canonicalDefect b v L x - (canonicalHopping b v L x).re) /
        (1 - canonicalOverlap b v L x) - sigmaOdd x
  overlap_tendsto : Tendsto (canonicalOverlap b v L) atTop (𝓝 0)
  defect_small : canonicalDefect b v L =o[atTop] A
  sigmaEven_small : sigmaEven =o[atTop] A
  sigmaOdd_small : sigmaOdd =o[atTop] A

theorem CanonicalParitySchurData.transfer {b L slope : ℝ} {v : Potential}
    (hopping : LinearCosineAsymptotic (fun x => -(canonicalHopping b v L x).re) slope)
    (h : CanonicalParitySchurData b v L hopping.amplitude) :
    Tendsto (fun x => (oddEnergy b v L x - evenEnergy b v L x +
      2 * (canonicalHopping b v L x).re) / (2 * hopping.amplitude x)) atTop (𝓝 0) := by
  apply parity_schur_transfer
    ((eventually_ge_atTop hopping.threshold).mono fun x hx => (hopping.amplitude_pos x hx).ne')
    ((eventually_ge_atTop h.threshold).mono h.even_equation)
    ((eventually_ge_atTop h.threshold).mono h.odd_equation)
    h.overlap_tendsto _ h.defect_small h.sigmaEven_small h.sigmaOdd_small
  simpa using hopping.isBigO_amplitude.neg_left

end InfiniteZero
