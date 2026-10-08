import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.CanonicalChannelAsymptotics

/-!
# The canonical hopping asymptotic under the documented classical inputs

The four conditional interfaces are instantiated here: operator realization,
the free resolvent, radial harmonic data and the proved elliptic estimate.
Only A002, A003 and A004 remain admitted. All source estimates, contour
arguments, saddle evaluation and channel assembly are
proved in the conditional modules. No tunneling asymptotic is admitted.
The potential parameters remain fixed before the separation threshold and
the subsequent choice of separation. Hopping continuity and the spectral
conclusions are constructed separately and joined in `ConstructedMainProof`.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

/-- The actual canonical hopping has the proved cosine asymptotic with the
explicit positive envelope and phase, for the fixed constructed potential. -/
theorem canonicalHopping_asymptotic {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) :
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
  let χ := Classical.choice (exists_cuspWeightCutoffs hp)
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential := by
    intro coupling
    exact magnetic_realization p.b coupling p.potential
      (admissiblePotential hp).smooth (admissiblePotential hp).bounded
  have hKernel : HasPositiveLandauResolvent p.b :=
    fun _ _ hCoupling hE => free_landau_resolvent_kernel hp.b_pos hCoupling hE
  exact exists_canonicalHopping_asymptotic_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot hKernel χ cert hL

/-- One geometric separation threshold is chosen for the fixed potential;
all later separations have the canonical hopping asymptotic. -/
theorem exists_canonicalHopping_asymptotic_separation
    {p : CuspParameters} (hp : p.BasicConditions) :
    ∃ cert : p.SeparationCertificate, ∀ L : ℝ, cert.L₀ ≤ L →
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
  obtain ⟨cert⟩ := exists_separationCertificate hp
  exact ⟨cert, fun _ hL => canonicalHopping_asymptotic hp cert hL⟩

end InfiniteZero.CuspParameters
