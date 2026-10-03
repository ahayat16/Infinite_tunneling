import InfiniteZero.IncomingCellAsymptotic
import InfiniteZero.ActiveSaddleEnvelopeComparison

/-!
# The incoming cell with the manuscript's positive Hessian envelope

Only the scalar saddle size changes. The ratio tends to one and is
absorbed into a remainder independent of the two source strengths and
the radial representative. No division by a physical source strength is
used, so the exact identity includes vanishing strengths as well.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

def activeIncomingTexRelativeError (p : CuspParameters) (L coupling : ℝ) : ℂ :=
  ((logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹ ^ 2 /
      logFlatSaddleTexSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹ ^ 2 : ℝ) : ℂ) *
    (1 + p.activeIncomingRelativeError L coupling) - 1

theorem tendsto_activeIncomingTexRelativeError_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    Tendsto (p.activeIncomingTexRelativeError L) atTop (𝓝 0) := by
  have hratio := (tendsto_logFlatSaddleLeadingSize_sq_div_texSize_sq (k := (2 : ℝ))
    hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L)).comp
      tendsto_inv_atTop_nhdsGT_zero
  have hratioC := Complex.continuous_ofReal.continuousAt.tendsto.comp hratio
  have herr := tendsto_activeIncomingRelativeError_of_radialData hp hRad hAcore hApot hL
  simpa only [activeIncomingTexRelativeError, Function.comp_def, Complex.ofReal_one, add_zero,
    mul_one, sub_self] using (hratioC.mul (herr.const_add 1)).sub_const 1

theorem eventually_activeSaddleEnvelope_eq_tex_mul_ratio
    {p : CuspParameters} (hp : p.BasicConditions) (L : ℝ) :
    ∀ᶠ coupling : ℝ in atTop, ∀ c Γ : ℝ,
      p.activeSaddleEnvelope L coupling c Γ =
        p.activeSaddleTexEnvelope L coupling c Γ *
          (logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹ ^ 2 /
            logFlatSaddleTexSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹ ^ 2) := by
  have hs := tendsto_inv_atTop_nhdsGT_zero.eventually
    (eventually_logFlatSaddleLeadingSize_sq_bounds (k := (2 : ℝ)) hp.β_pos
      (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L))
  filter_upwards [hs] with coupling hc
  intro c Γ
  have hne := hc.1.ne'
  dsimp only [activeSaddleEnvelope, activeSaddleTexEnvelope]
  field_simp
  simp [one_div, hne]

theorem eventually_incoming_sourceCell_Tex_asymptotic_of_radialData
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
            p.activeSaddleTexEnvelope L coupling c Γ : ℝ) : ℂ) *
          Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) *
            (1 + p.activeIncomingTexRelativeError L coupling) := by
  filter_upwards [eventually_incoming_sourceCell_asymptotic_of_radialData
      hp hRad hAcore hApot hL,
    eventually_activeSaddleEnvelope_eq_tex_mul_ratio hp L] with coupling hcell henv
  intro c Γ φ hφ htail
  rw [hcell c Γ φ hφ htail, henv c Γ]
  dsimp only [activeIncomingTexRelativeError]
  push_cast
  ring

end InfiniteZero.CuspParameters
