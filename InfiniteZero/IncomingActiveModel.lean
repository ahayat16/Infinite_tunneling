import InfiniteZero.IncomingCuspNormalizationBounds
import InfiniteZero.CuspTangentialMass
import InfiniteZero.ComplexSaddleNormalization

/-!
# The explicit complex leading model for the incoming cusp integral

The full and radial-core energies stay separate in the three kernel
coefficients and the real action. The two normal factors are multiplied
as complex quantities, retaining the doubled saddle phase.
-/

noncomputable section

namespace InfiniteZero

/-- The source scaling and three two-dimensional kernels give precisely
the thirteen-halves coupling power, without any asymptotic replacement. -/
theorem incoming_prefactor_rpow_identity {h : ℝ} (hh : 0 < h) :
    (h ^ 2)⁻¹ / (h ^ (3 / 2 : ℝ)) ^ 3 = (h⁻¹) ^ 6 * Real.sqrt h⁻¹ := by
  have hpow : h ^ (3 / 2 : ℝ) = h * Real.sqrt h := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hh,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  let s := Real.sqrt h
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hs2 : s ^ 2 = h := Real.sq_sqrt hh.le
  rw [hpow, Real.sqrt_inv]
  change (h ^ 2)⁻¹ / (h * s) ^ 3 = (h⁻¹) ^ 6 * s⁻¹
  rw [← hs2]
  field_simp

namespace CuspParameters

def incomingCuspLeadingModel (p : CuspParameters) (L h Ecore Efull : ℝ) : ℂ :=
  ((landauLeadingCoefficient p.b Ecore p.R ^ 2 *
      landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L) *
      p.cuspTangentialMass ^ 2 / (h ^ (3 / 2 : ℝ)) ^ 3 : ℝ) : ℂ) *
    Complex.exp ((-(p.activeReferenceAction L Efull Ecore : ℂ) +
      Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) *
    logFlatSaddleLeading p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2

theorem incomingCuspNormalization_mul_leadingModel
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    p.incomingCuspNormalization L h Ecore Efull * p.incomingCuspLeadingModel L h Ecore Efull =
      (p.cuspTangentialMass ^ 2 : ℝ) *
        logFlatSaddleLeading p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 := by
  have hkR : (landauLeadingCoefficient p.b Ecore p.R : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (landauLeadingCoefficient_pos hp.b_pos hEc hp.radius_pos).ne'
  have hkD : (landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (landauLeadingCoefficient_pos hp.b_pos hEf
      (Geometry.activeDistance_pos hL)).ne'
  have hH : ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hh _).ne'
  have he :
      Complex.exp (((p.activeReferenceAction L Efull Ecore : ℂ) -
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) *
        Complex.exp ((-(p.activeReferenceAction L Efull Ecore : ℂ) +
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    rw [show ((p.activeReferenceAction L Efull Ecore : ℂ) -
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ) +
        (-(p.activeReferenceAction L Efull Ecore : ℂ) +
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ) = 0 by ring]
    exact Complex.exp_zero
  unfold incomingCuspNormalization incomingCuspLeadingModel
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  calc
    _ = ((((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 3 /
        ((landauLeadingCoefficient p.b Ecore p.R : ℂ) ^ 2 *
          (landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L) : ℂ))) *
        ((landauLeadingCoefficient p.b Ecore p.R : ℂ) ^ 2 *
          (landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L) : ℂ) *
          (p.cuspTangentialMass : ℂ) ^ 2 / ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 3)) *
        (Complex.exp (((p.activeReferenceAction L Efull Ecore : ℂ) -
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) *
        Complex.exp ((-(p.activeReferenceAction L Efull Ecore : ℂ) +
          Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ))) *
        logFlatSaddleLeading p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 := by ring
    _ = _ := by rw [he]; field_simp

theorem incomingCuspLeadingModel_normalized
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull)
    (hr : 0 < (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).re) :
    logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
        p.incomingCuspNormalization L h Ecore Efull * p.incomingCuspLeadingModel L h Ecore Efull =
      (p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ) * (p.cuspTangentialMass ^ 2 : ℝ) := by
  rw [mul_assoc, incomingCuspNormalization_mul_leadingModel hp hL hh hEc hEf]
  calc
    _ = (logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
        logFlatSaddleLeading p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2) *
        (p.cuspTangentialMass ^ 2 : ℝ) := by ring
    _ = _ := by rw [logFlatSaddleNormalizer_sq_mul_leading_sq_two hp.β_pos hr]

end CuspParameters
end InfiniteZero
