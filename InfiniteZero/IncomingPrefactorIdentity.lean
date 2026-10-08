import InfiniteZero.IncomingActiveModel
import InfiniteZero.ActiveIncomingPhase

/-!
# Exact amplitude and phase of the incoming source model

Both source strengths remain multiplicative, including when either is
zero. The source sign is retained. The coefficient ratio divides only by
the fixed positive limiting kernel and tangential coefficient.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

theorem incomingCuspLeadingModel_source_prefactor
    (p : CuspParameters) (L : ℝ) {coupling : ℝ} (hcoupling : 0 < coupling) (c Γ : ℝ) :
    let Ec := -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)
    let Ef := scaledAtomicEnergy p coupling
    let K := landauLeadingCoefficient p.b Ec p.R ^ 2 *
      landauLeadingCoefficient p.b Ef (Geometry.activeDistance p.R L) * p.cuspTangentialMass ^ 2;
    -(((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        ((((coupling⁻¹) ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        p.incomingCuspLeadingModel L coupling⁻¹ Ec Ef =
      -((K * p.activeSaddleEnvelope L coupling c Γ : ℝ) : ℂ) *
        Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) := by
  let Ec := -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)
  let Ef := scaledAtomicEnergy p coupling
  let K := landauLeadingCoefficient p.b Ec p.R ^ 2 *
    landauLeadingCoefficient p.b Ef (Geometry.activeDistance p.R L) * p.cuspTangentialMass ^ 2
  let A := p.activeReferenceAction L Ef Ec
  let H := (coupling⁻¹) ^ (3 / 2 : ℝ)
  let S := logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹
  let G := logFlatSaddleLeading p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hcoupling
  have hH : H ≠ 0 := (Real.rpow_pos_of_pos hh _).ne'
  have hscale : (((coupling⁻¹) ^ 2)⁻¹ / H ^ 3) =
      coupling ^ 6 * Real.sqrt coupling := by
    simpa only [H, inv_inv] using incoming_prefactor_rpow_identity hh
  have hscalar :
      -((coupling⁻¹) ^ 2) * (((coupling⁻¹) ^ 2)⁻¹ * p.ε * p.a * c * Γ) ^ 2 *
        (K / H ^ 3) =
      -K * (p.ε ^ 2 * p.a ^ 2 * c ^ 2 * Γ ^ 2 * coupling ^ 6 * Real.sqrt coupling) := by
    calc
      _ = -K * (p.ε ^ 2 * p.a ^ 2 * c ^ 2 * Γ ^ 2) *
          (((coupling⁻¹) ^ 2)⁻¹ / H ^ 3) := by field_simp
      _ = _ := by rw [hscale]; ring
  have hexp :
      Complex.exp ((-(A : ℂ) + Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) /
        ((coupling⁻¹ : ℝ) : ℂ)) =
      (Real.exp (-coupling * A) : ℂ) *
        Complex.exp (((coupling * Geometry.phaseStar p.b p.R L : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [div_inv_eq_mul]
    ring
  have hphase :
      Complex.exp (((coupling * Geometry.phaseStar p.b p.R L : ℝ) : ℂ) * Complex.I) * G ^ 2 =
        (S ^ 2 : ℝ) * Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) :=
    exp_geometric_mul_logFlatSaddleLeading_sq p L coupling
  change -(((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        ((((coupling⁻¹) ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        ((K / H ^ 3 : ℝ) *
          Complex.exp ((-(A : ℂ) + Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) /
            ((coupling⁻¹ : ℝ) : ℂ)) * G ^ 2) = _
  rw [hexp]
  calc
    _ = ((-((coupling⁻¹) ^ 2) * (((coupling⁻¹) ^ 2)⁻¹ * p.ε * p.a * c * Γ) ^ 2 *
        (K / H ^ 3) : ℝ) : ℂ) * (Real.exp (-coupling * A) : ℂ) *
        (Complex.exp (((coupling * Geometry.phaseStar p.b p.R L : ℝ) : ℂ) * Complex.I) * G ^ 2) := by
      push_cast
      ring
    _ = _ := by
      rw [hscalar, hphase]
      dsimp only [activeSaddleEnvelope, A, K, Ec, Ef, S]
      push_cast
      ring

theorem incomingCuspLeadingModel_source_prefactor_relative
    {p : CuspParameters} (hp : p.BasicConditions) {L coupling : ℝ}
    (hL : p.R < 2 * L) (hcoupling : 0 < coupling) (c Γ : ℝ) :
    let Ec := -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)
    let Ef := scaledAtomicEnergy p coupling
    let K := landauLeadingCoefficient p.b Ec p.R ^ 2 *
      landauLeadingCoefficient p.b Ef (Geometry.activeDistance p.R L) * p.cuspTangentialMass ^ 2;
    -(((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        ((((coupling⁻¹) ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        p.incomingCuspLeadingModel L coupling⁻¹ Ec Ef =
      -((K / p.activeTangentialLeadingCoefficient L : ℝ) : ℂ) *
        ((p.activeTangentialLeadingCoefficient L * p.activeSaddleEnvelope L coupling c Γ : ℝ) : ℂ) *
        Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) := by
  dsimp only
  rw [incomingCuspLeadingModel_source_prefactor p L hcoupling c Γ]
  have hK : (p.activeTangentialLeadingCoefficient L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (activeTangentialLeadingCoefficient_pos hp hL).ne'
  push_cast
  field_simp

end InfiniteZero.CuspParameters
