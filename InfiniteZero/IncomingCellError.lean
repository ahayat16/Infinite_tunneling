import InfiniteZero.AtomicIncomingIntegralAsymptotic
import InfiniteZero.CuspTangentialMass

/-!
# Relative errors for the actual incoming cell

The first remainder belongs to the physical four-coordinate integral.
The second also replaces the moving positive kernel coefficient by its
limit. Both depend only on the fixed potential, separation and coupling;
neither depends on the radial tail coefficient, Schur coefficient, or
choice of a radial wavefunction representative.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

def incomingCuspRelativeError (p : CuspParameters) (L h : ℝ) : ℂ :=
  let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
  let Ef := scaledAtomicEnergy p h⁻¹
  (logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
    p.incomingCuspNormalization L h Ec Ef * p.incomingCuspIntegral L h Ec Ef) /
      ((p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ) * (p.cuspTangentialMass ^ 2 : ℝ)) - 1

theorem tendsto_incomingCuspRelativeError_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    Tendsto (p.incomingCuspRelativeError L) (𝓝[>] 0) (𝓝 0) := by
  simpa only [incomingCuspRelativeError, sub_self] using
    (tendsto_atomic_incomingCuspIntegral_relative_of_radialData
      hp hRad hAcore hApot hL).sub_const (1 : ℂ)

def movingActiveTangentialCoefficient (p : CuspParameters) (L coupling : ℝ) : ℝ :=
  landauLeadingCoefficient p.b
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R ^ 2 *
    landauLeadingCoefficient p.b (scaledAtomicEnergy p coupling)
      (Geometry.activeDistance p.R L) * p.cuspTangentialMass ^ 2

theorem tendsto_movingActiveTangentialCoefficient_relative_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    Tendsto (fun coupling : ℝ => p.movingActiveTangentialCoefficient L coupling /
      p.activeTangentialLeadingCoefficient L) atTop (𝓝 1) := by
  have hcore := (tendsto_semiclassicalCoreEnergy_of_radialData
    hp hRad hAcore hApot).comp tendsto_inv_atTop_nhdsGT_zero
  simp only [Function.comp_def, inv_inv] at hcore
  exact tendsto_activeTangentialLeadingCoefficient_relative hp hL hcore
    (tendsto_scaledAtomicEnergy_of_radialData hp hRad hAcore hApot)

def activeIncomingRelativeError (p : CuspParameters) (L coupling : ℝ) : ℂ :=
  ((p.movingActiveTangentialCoefficient L coupling /
    p.activeTangentialLeadingCoefficient L : ℝ) : ℂ) *
      (1 + p.incomingCuspRelativeError L coupling⁻¹) - 1

theorem tendsto_activeIncomingRelativeError_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    Tendsto (p.activeIncomingRelativeError L) atTop (𝓝 0) := by
  have hk := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_movingActiveTangentialCoefficient_relative_of_radialData
      hp hRad hAcore hApot hL)
  have he := (tendsto_incomingCuspRelativeError_of_radialData
    hp hRad hAcore hApot hL).comp tendsto_inv_atTop_nhdsGT_zero
  simpa only [activeIncomingRelativeError, Function.comp_def, Complex.ofReal_one,
    add_zero, mul_one, sub_self] using (hk.mul (he.const_add (1 : ℂ))).sub_const (1 : ℂ)

end InfiniteZero.CuspParameters
