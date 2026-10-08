import InfiniteZero.ConcreteChannelWitnesses
import InfiniteZero.IncomingCellTexAsymptotic
import InfiniteZero.CanonicalChannelAssembly
import InfiniteZero.CanonicalChannelErrors
import InfiniteZero.CanonicalHoppingFromChannels

/-!
# Constructing the canonical channel asymptotic for the cusp potential

The actual radial and full ground-state witnesses are chosen together.
The incoming integral asymptotic, the scattered response estimate and all
seven inactive estimates are applied to those same witnesses. No channel
or tunneling asymptotic is an input of the final existence theorem.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem exists_canonicalChannelAsymptotics_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ W : ConcreteChannelWitnesses p L,
      ∃ H : ChannelAsymptotics (canonicalSourceCell p L) (Geometry.phaseStar p.b p.R L),
        0 < H.threshold ∧
        H.amplitude = (fun coupling => p.activeTangentialLeadingCoefficient L *
          p.activeSaddleTexEnvelope L coupling (W.c coupling) (W.Γ coupling)) ∧
        H.phase = p.activeIncomingPhase L := by
  obtain ⟨W⟩ := exists_concreteChannelWitnesses_of_radialData
    hInterior hp hRad hAcore hApot χ cert hL
  have hRL : p.R < L :=
    (lt_of_le_of_lt (le_max_right _ _) cert.separation).trans_le hL
  have hsep : p.R < 2 * L := by linarith [hp.radius_pos]
  let K := p.activeTangentialLeadingCoefficient L
  have hK : 0 < K := activeTangentialLeadingCoefficient_pos hp hsep
  let amplitude := fun coupling => K *
    p.activeSaddleTexEnvelope L coupling (W.c coupling) (W.Γ coupling)
  let incoming := fun coupling => sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling)
    (fun x => (W.c coupling : ℂ) * W.φ coupling x) 1 2
  let activeError := fun coupling => (W.Cactive / K) *
    Real.exp (-(p.β / 8) * (Real.log coupling) ^ 2)
  let inactiveError := fun coupling => (W.Cinactive / K) *
    Real.exp (-15 * p.hopMargin * coupling)
  have ha : ∀ᶠ coupling in atTop, 0 < amplitude coupling := by
    filter_upwards [eventually_ge_atTop W.threshold] with coupling hc
    exact mul_pos hK (W.envelope_pos coupling hc)
  have hi : ∀ᶠ coupling in atTop,
      incoming coupling = -(amplitude coupling : ℂ) *
        Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) *
          (1 + p.activeIncomingTexRelativeError L coupling) := by
    filter_upwards [eventually_incoming_sourceCell_Tex_asymptotic_of_radialData
      hp hRad hAcore hApot hsep, eventually_ge_atTop W.threshold] with coupling hi hc
    exact hi (W.c coupling) (W.Γ coupling) (W.φ coupling)
      (W.core_ground coupling hc).1.1.continuous (W.tail coupling hc)
  have hactive : ∀ᶠ coupling in atTop,
      ‖canonicalSourceCell p L coupling 1 2 - incoming coupling‖ ≤
        amplitude coupling * activeError coupling := by
    filter_upwards [eventually_ge_atTop W.threshold] with coupling hc
    have hb := W.active_bound coupling hc
    convert hb using 1
    dsimp only [amplitude, activeError]
    field_simp
  have hinactive : ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
      ∀ᶠ coupling in atTop, ‖canonicalSourceCell p L coupling i j‖ ≤
        amplitude coupling * inactiveError coupling := by
    intro i j h₁ h₂
    filter_upwards [eventually_ge_atTop W.threshold] with coupling hc
    have hb := W.inactive_bound coupling hc i j h₁ h₂
    convert hb using 1
    dsimp only [amplitude, inactiveError]
    field_simp
  obtain ⟨Tp, _hTp, hpcont⟩ := exists_continuousOn_activeIncomingPhase p L
  obtain ⟨H, hH, hamp, hphase⟩ :=
    exists_canonicalChannelAsymptotics_of_eventual_relative_errors p L
      (Geometry.phaseStar p.b p.R L) amplitude (p.activeIncomingPhase L) incoming
      (p.activeIncomingTexRelativeError L) activeError inactiveError ha ⟨Tp, hpcont⟩
      (tendsto_activeIncomingPhase_div hp L)
      (tendsto_activeIncomingTexRelativeError_of_radialData hp hRad hAcore hApot hsep)
      hi (tendsto_active_scattered_relative_rate hp L W.Cactive) hactive
      (tendsto_inactive_relative_rate hp L W.Cinactive) hinactive
  exact ⟨W, H, hH, hamp, hphase⟩

/-- The hopping cosine formula for the actual potential, with its concrete
positive envelope and phase. Continuity and spectral splitting are separate
obligations; neither is encoded as an unproved input here. -/
theorem exists_canonicalHopping_asymptotic_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hKernel : HasPositiveLandauResolvent p.b)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ W : ConcreteChannelWitnesses p L,
      ∃ H : LinearCosineAsymptotic
          (fun coupling => -(canonicalHopping p.b p.potential L coupling).re)
          (Geometry.phaseStar p.b p.R L),
        0 < H.threshold ∧
        H.amplitude = (fun coupling => 2 * (p.activeTangentialLeadingCoefficient L *
          p.activeSaddleTexEnvelope L coupling (W.c coupling) (W.Γ coupling))) ∧
        H.phase = p.activeIncomingPhase L ∧
        ∀ coupling, H.threshold ≤ coupling →
          (canonicalHopping p.b p.potential L coupling).im = 0 := by
  obtain ⟨W, Hc, _hHc, hamp, hphase⟩ := exists_canonicalChannelAsymptotics_of_radialData
    hInterior hp hRad hAcore hApot χ cert hL
  have hRL : p.R < L :=
    (lt_of_le_of_lt (le_max_right _ _) cert.separation).trans_le hL
  have hsep : p.R < 2 * L := by linarith [hp.radius_pos]
  obtain ⟨H, ha, hp', hT, _hTc, hreal⟩ :=
    exists_canonicalHopping_linearCosine_of_channels_of_radialData
      hp hRad hAcore hApot hKernel hsep Hc
  refine ⟨W, H, hT, ?_, hp'.trans hphase, hreal⟩
  rw [ha, hamp]

end InfiniteZero.CuspParameters
