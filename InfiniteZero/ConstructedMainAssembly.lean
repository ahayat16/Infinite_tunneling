import InfiniteZero.ConstructedDoubleWellSpectral
import InfiniteZero.ConstructedParityEnergyContinuity
import InfiniteZero.HoppingContinuity
import InfiniteZero.OperatorMain

/-!
# Final conditional assembly from the actual hopping and Schur data

All atomic, two-mode and continuity fields are supplied by their proved
constructions. Only the explicit hopping asymptotic and its matching physical
Schur data are arguments here. This helper does not assert their existence.
-/

noncomputable section
open Set
namespace InfiniteZero

theorem TwoModeRealization.mono_threshold {b L T T' : ℝ} {v : Potential}
    (h : TwoModeRealization b v L T) (hTT' : T ≤ T') :
    TwoModeRealization b v L T' where
  ordered_ground coupling hc := h.ordered_ground coupling (hTT'.trans hc)
  ordered_second coupling hc := h.ordered_second coupling (hTT'.trans hc)
  crossing_modes coupling hc := h.crossing_modes coupling (hTT'.trans hc)
  even_mode coupling hc := h.even_mode coupling (hTT'.trans hc)
  odd_mode coupling hc := h.odd_mode coupling (hTT'.trans hc)

namespace CuspParameters

theorem nonempty_localAnalyticData_of_hopping_schur
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L))
    {L : ℝ} (hL : cert.L₀ ≤ L)
    (H : LinearCosineAsymptotic
      (fun coupling => -(canonicalHopping p.b p.potential L coupling).re)
      (Geometry.phaseStar p.b p.R L))
    (hreal : ∀ coupling, H.threshold ≤ coupling →
      (canonicalHopping p.b p.potential L coupling).im = 0)
    (hSchur : CanonicalParitySchurData p.b p.potential L H.amplitude) :
    Nonempty (LocalAnalyticData p.b p.potential L (Geometry.phaseStar p.b p.R L)) := by
  obtain ⟨Ta, hTa, hatomic⟩ :=
    eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  obtain ⟨Tm, _hTm, hmodes⟩ := exists_doubleWell_twoModeRealization_of_radialData
    hp cert hRad hAcore hApot hAleft hAright hAdouble
  obtain ⟨Tc, _hTc, hcontinuous⟩ :=
    exists_canonicalHopping_continuous_of_radialData hp hRad hAcore hApot
  let T := max (max Ta Tm) (max Tc H.threshold)
  have ha : Ta ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hm : Tm ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hc : Tc ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hH : H.threshold ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hT : 0 < T := hTa.trans_le ha
  refine ⟨{
    threshold := T
    atomic_exists := fun coupling hcoupling => (hatomic coupling (ha.trans hcoupling)).1
    atomic_simple := fun coupling hcoupling => (hatomic coupling (ha.trans hcoupling)).2.1
    modes := (hmodes L hL).1.mono_threshold hm
    ground_gap := fun coupling hcoupling => (hmodes L hL).2 coupling (hm.trans hcoupling)
    hopping_real := fun coupling hcoupling => hreal coupling (hH.trans hcoupling)
    hopping_asymptotic := H
    schur := hSchur
    continuity_threshold := T
    splitting_continuous := ?_
    hopping_continuous := ?_
  }⟩
  · exact (continuousOn_signedSplitting_of_radialData
      hp cert hRad hAcore hApot hAleft hAright hAdouble L hL).mono
        (fun _ hx => hT.trans_le hx)
  · exact Complex.continuous_re.comp_continuousOn
      ((hcontinuous L).mono (fun _ hx => hc.trans hx))

/-- Conditional final conclusion: the actual hopping asymptotic and the
matching relative Schur estimates remain explicit inputs. -/
theorem operatorMainConclusion_of_hopping_schur
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L))
    {L : ℝ} (hL : cert.L₀ ≤ L)
    (H : LinearCosineAsymptotic
      (fun coupling => -(canonicalHopping p.b p.potential L coupling).re)
      (Geometry.phaseStar p.b p.R L))
    (hreal : ∀ coupling, H.threshold ≤ coupling →
      (canonicalHopping p.b p.potential L coupling).im = 0)
    (hSchur : CanonicalParitySchurData p.b p.potential L H.amplitude) :
    OperatorMainConclusion p.b p.potential L := by
  obtain ⟨h⟩ := nonempty_localAnalyticData_of_hopping_schur hp cert hRad
    hAcore hApot hAleft hAright hAdouble hL H hreal hSchur
  have hphase : 0 < Geometry.phaseStar p.b p.R L :=
    phase_pos hp ((le_max_right _ _).trans_lt cert.separation) hL
  exact (h.conclusion hphase).toOperator hApot (fun coupling => hAdouble coupling L)
    ⟨h.threshold, h.ground_gap⟩

end CuspParameters
end InfiniteZero
