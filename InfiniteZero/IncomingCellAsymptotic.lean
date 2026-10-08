import InfiniteZero.IncomingCellError
import InfiniteZero.IncomingPrefactorIdentity

/-!
# The actual incoming source cell, including its phase and amplitude

The normalized physical integral is reconstructed exactly from its proved
relative error. The source identity then restores the negative sign and
the coupling power. The remainder is independent of both source strengths
and of the radial wavefunction representative.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem incomingCuspIntegral_eq_leadingModel_mul_error
    {p : CuspParameters} (hp : p.BasicConditions) {L h : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h)
    (hEc : 0 < -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
    (hEf : 0 < scaledAtomicEnergy p h⁻¹)
    (hr : 0 < (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).re) :
    let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
    let Ef := scaledAtomicEnergy p h⁻¹
    p.incomingCuspIntegral L h Ec Ef =
      p.incomingCuspLeadingModel L h Ec Ef * (1 + p.incomingCuspRelativeError L h) := by
  dsimp only
  let Z := logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
    p.incomingCuspNormalization L h
      (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹)
  let C : ℂ := (p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ) * (p.cuspTangentialMass ^ 2 : ℝ)
  have hC : C ≠ 0 := incomingCusp_leading_coefficient_ne_zero hp
  have hid := incomingCuspLeadingModel_normalized hp hL hh hEc hEf hr
  have hZ : Z ≠ 0 := (mul_ne_zero_iff.mp (show Z *
      p.incomingCuspLeadingModel L h
        (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹) ≠ 0 by
    rw [hid]
    exact hC)).1
  apply mul_left_cancel₀ hZ
  rw [← mul_assoc, hid]
  change Z * p.incomingCuspIntegral L h
      (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹) =
    C * (1 + (Z * p.incomingCuspIntegral L h
      (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹) / C - 1))
  field_simp
  ring

theorem incoming_sourceCell_eq_activeSaddleEnvelope_mul_error
    {p : CuspParameters} (hp : p.BasicConditions) {L coupling : ℝ}
    (hL : p.R < 2 * L) (hcoupling : 0 < coupling)
    (hEc : 0 < -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
    (hEf : 0 < scaledAtomicEnergy p coupling)
    (hr : 0 < (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹).re)
    (c Γ : ℝ) (φ : Wavefunction) (hφ : Continuous φ)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b coupling⁻¹
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) :
    sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling)
        (fun x => (c : ℂ) * φ x) 1 2 =
      -((p.activeTangentialLeadingCoefficient L *
          p.activeSaddleEnvelope L coupling c Γ : ℝ) : ℂ) *
        Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) *
          (1 + p.activeIncomingRelativeError L coupling) := by
  have hid := incomingCuspIntegral_eq_leadingModel_mul_error hp hL
    (inv_pos.mpr hcoupling) (by simpa only [inv_inv] using hEc)
      (by simpa only [inv_inv] using hEf) hr
  simp only [inv_inv] at hid
  rw [incoming_sourceCell_eq_incomingCuspIntegral hp hL (inv_pos.mpr hcoupling)
    hEc hEf c Γ φ hφ htail, hid, ← mul_assoc,
    incomingCuspLeadingModel_source_prefactor_relative hp hL hcoupling c Γ]
  dsimp only [activeIncomingRelativeError, movingActiveTangentialCoefficient]
  ring

/-- A single coupling threshold works for every radial representative and
every pair of source strengths. The error itself tends to zero by
`tendsto_activeIncomingRelativeError_of_radialData`. -/
theorem eventually_incoming_sourceCell_asymptotic_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ coupling : ℝ in atTop, ∀ c Γ : ℝ, ∀ φ : Wavefunction, Continuous φ →
      (∀ x : Plane, p.r₀ < ‖x‖ →
        φ x = (Γ * landauKernel p.b coupling⁻¹
          (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) →
      sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling)
          (fun x => (c : ℂ) * φ x) 1 2 =
        -((p.activeTangentialLeadingCoefficient L *
            p.activeSaddleEnvelope L coupling c Γ : ℝ) : ℂ) *
          Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) *
            (1 + p.activeIncomingRelativeError L coupling) := by
  obtain ⟨T, _hT, henergies⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  have hroot := tendsto_inv_atTop_nhdsGT_zero.eventually
    (eventually_logFlatSaddleRoot_equation (k := (2 : ℝ)) hp.β_pos.ne'
      (hp.t₀_pos.trans hp.t₀_lt).ne' (activeSaddleSlope_ne_zero hp L))
  filter_upwards [eventually_ge_atTop T, eventually_gt_atTop (0 : ℝ), hroot]
    with coupling hT hc hr
  have hE := henergies coupling hT
  exact incoming_sourceCell_eq_activeSaddleEnvelope_mul_error hp hL hc
    (by linarith [hE.2.1.1]) (by linarith [hE.1.1]) (by linarith [hr.1])

end InfiniteZero.CuspParameters
