import InfiniteZero.ComplexCuspKernelProductProfile
import InfiniteZero.ComplexCuspFrozenSlope

/-!
# Uniform incoming multiplier with the true atomic energies

The fixed normal slope is the same one as in the saddle envelope. Only
that slope is frozen: the full/core actions and leading kernel coefficients
retain their actual coupling-dependent energies. The spectral O(h) rate
is proved from the radial data and the constructed full atomic operator.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

def frozenCuspKernelPhaseProfile (p : CuspParameters)
    (L h Ecore Efull s r : ℝ) (t u : ℂ) : ℂ :=
  Geometry.complexCuspKernelPhaseProfile p.b h Ecore Efull p.R L s r t u *
    complexSlopeFreezingFactor (p.activeSaddleSlope L)
      (p.movingActiveSaddleSlope L Ecore Efull) h t u

/-- Exact normalization of the true kernel product, with its full magnetic
phase and with only the linear slope replaced by the fixed saddle slope. -/
theorem frozenCuspKernelPhaseProfile_eq_normalized_product
    (p : CuspParameters) (L h Ecore Efull s r : ℝ) (t u : ℂ) :
    p.frozenCuspKernelPhaseProfile L h Ecore Efull s r t u =
      ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 3 /
        ((landauLeadingCoefficient p.b Ecore p.R : ℂ) ^ 2 *
          (landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L) : ℂ)) *
      Complex.exp (((p.activeReferenceAction L Efull Ecore : ℝ) : ℂ) / (h : ℂ) +
        (p.activeSaddleSlope L * (t + u) -
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) *
      (Geometry.complexCuspKernelProduct p.b h Ecore Ecore Efull p.R L s r (t, u) *
        Complex.exp (Complex.I * Geometry.complexPhase p.b L
          (Geometry.complexCuspPlus p.R s t) (Geometry.complexCuspMinus p.R r u) / (h : ℂ))) := by
  rw [frozenCuspKernelPhaseProfile,
    Geometry.complexCuspKernelPhaseProfile_eq_normalized_product, complexSlopeFreezingFactor]
  have he :
      Complex.exp ((2 * (bridgeAction p.b Ecore p.R : ℂ) +
        (bridgeAction p.b Efull (Geometry.activeDistance p.R L) : ℂ) +
        ((((deriv (bridgeAction p.b Ecore) p.R : ℝ) : ℂ) +
          ((deriv (bridgeAction p.b Efull) (Geometry.activeDistance p.R L) : ℝ) : ℂ)) / 2 -
            Complex.I * (Geometry.phaseSlope p.b L : ℂ)) * (t + u) -
        Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) *
      Complex.exp ((p.activeSaddleSlope L - p.movingActiveSaddleSlope L Ecore Efull) *
        (t + u) / (h : ℂ)) =
      Complex.exp (((p.activeReferenceAction L Efull Ecore : ℝ) : ℂ) / (h : ℂ) +
        (p.activeSaddleSlope L * (t + u) -
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [movingActiveSaddleSlope, activeReferenceAction]
    push_cast
    ring
  calc
    _ = (((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 3 /
        ((landauLeadingCoefficient p.b Ecore p.R : ℂ) ^ 2 *
          (landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L) : ℂ))) *
        (Complex.exp ((2 * (bridgeAction p.b Ecore p.R : ℂ) +
          (bridgeAction p.b Efull (Geometry.activeDistance p.R L) : ℂ) +
          ((((deriv (bridgeAction p.b Ecore) p.R : ℝ) : ℂ) +
            ((deriv (bridgeAction p.b Efull) (Geometry.activeDistance p.R L) : ℝ) : ℂ)) / 2 -
              Complex.I * (Geometry.phaseSlope p.b L : ℂ)) * (t + u) -
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) *
        Complex.exp ((p.activeSaddleSlope L - p.movingActiveSaddleSlope L Ecore Efull) *
          (t + u) / (h : ℂ))) *
        (Geometry.complexCuspKernelProduct p.b h Ecore Ecore Efull p.R L s r (t, u) *
          Complex.exp (Complex.I * Geometry.complexPhase p.b L
            (Geometry.complexCuspPlus p.R s t) (Geometry.complexCuspMinus p.R r u) / (h : ℂ))) := by
      ring
    _ = _ := by rw [he]

theorem tendsto_semiclassicalCoreEnergy_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    Tendsto (fun h : ℝ => -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨T, _hT, hbound⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun h : ℝ => hRad.energyBound * h)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T)] with h hh
    simpa only [Real.norm_eq_abs, inv_inv, div_inv_eq_mul] using (hbound h⁻¹ hh).2.2.2
  · simpa using (tendsto_nhdsWithin_of_tendsto_nhds
      (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0))).const_mul hRad.energyBound

/-- A single small-scale threshold controls the actual coupled multiplier
for all bounded tangential coordinates and all complex normal coordinates
in the active window. There is no assumed profile estimate here. -/
theorem eventually_atomic_frozenCuspKernelPhaseProfile_uniform_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ t u : ℂ, ‖t‖ ≤ M * logFlatActiveWindow p.tStar h →
        ‖u‖ ≤ M * logFlatActiveWindow p.tStar h →
        ‖p.frozenCuspKernelPhaseProfile L h
          (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
          (scaledAtomicEnergy p h⁻¹) s r t u - 1‖ < ε := by
  have hEc := tendsto_semiclassicalCoreEnergy_of_radialData hp hRad hAcore hApot
  have hEf := (tendsto_scaledAtomicEnergy_of_radialData hp hRad hAcore hApot).comp
    tendsto_inv_nhdsGT_zero
  have htStar := hp.t₀_pos.trans hp.t₀_lt
  have hsmall : 0 < ε / 3 := div_pos hε (by norm_num)
  have hprofile := Geometry.eventually_complexCuspKernelPhaseProfile_uniform (M := M)
    hp.b_pos (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    hp.radius_pos hL hp.s₀_pos.le htStar hEc hEf hsmall
  have hnorm := Geometry.eventually_norm_complexCuspKernelPhaseProfile_le_two (M := M)
    hp.b_pos (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    hp.radius_pos hL hp.s₀_pos.le htStar hEc hEf
  have hfreeze := eventually_atomic_slopeFreezingFactor_uniform_of_radialData
    hp hRad hAcore hApot L hM hsmall
  filter_upwards [hprofile, hnorm, hfreeze] with h hph hnh hfh
  intro s r hs hr t u ht hu
  let A := Geometry.complexCuspKernelPhaseProfile p.b h
    (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
    (scaledAtomicEnergy p h⁻¹) p.R L s r t u
  let B := complexSlopeFreezingFactor (p.activeSaddleSlope L)
    (p.movingActiveSaddleSlope L (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
      (scaledAtomicEnergy p h⁻¹)) h t u
  have ha : ‖A - 1‖ < ε / 3 := hph s r hs hr t u ht hu
  have han : ‖A‖ ≤ 2 := hnh s r hs hr t u ht hu
  have hb : ‖B - 1‖ < ε / 3 := hfh t u ht hu
  have hprod : ‖A * B - 1‖ ≤ ‖A‖ * ‖B - 1‖ + ‖A - 1‖ := by
    calc
      _ = ‖A * (B - 1) + (A - 1)‖ := by congr 1; ring
      _ ≤ _ := by simpa only [norm_mul] using norm_add_le (A * (B - 1)) (A - 1)
  change ‖A * B - 1‖ < ε
  nlinarith [mul_le_mul_of_nonneg_right han (norm_nonneg (B - 1))]

theorem eventually_norm_atomic_frozenCuspKernelPhaseProfile_le_two_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {M : ℝ} (hM : 0 ≤ M) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ t u : ℂ, ‖t‖ ≤ M * logFlatActiveWindow p.tStar h →
        ‖u‖ ≤ M * logFlatActiveWindow p.tStar h →
        ‖p.frozenCuspKernelPhaseProfile L h
          (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
          (scaledAtomicEnergy p h⁻¹) s r t u‖ ≤ 2 := by
  filter_upwards [eventually_atomic_frozenCuspKernelPhaseProfile_uniform_of_radialData
    hp hRad hAcore hApot hL hM (by norm_num : (0 : ℝ) < 1)] with h hh
  intro s r hs hr t u ht hu
  have hb := hh s r hs hr t u ht hu
  have hn := norm_sub_le (p.frozenCuspKernelPhaseProfile L h
    (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
    (scaledAtomicEnergy p h⁻¹) s r t u - 1) (-1)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at hn
  linarith

end InfiniteZero.CuspParameters
