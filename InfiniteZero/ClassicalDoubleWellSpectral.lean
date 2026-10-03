import InfiniteZero.ConstructedDoubleWellSpectral
import InfiniteZero.ClassicalDoubleWellParityGround

/-!
# Spectral realization and ground gap from only A002 and A004

This supplies the original spectral contract for the concrete cusp
potential. It assumes no spectral or tunneling estimate for that potential.
Only the universal realization and radial-core data are admitted.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem doubleWell_twoModeRealization {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ T > 0, ∀ L : ℝ, cert.L₀ ≤ L →
      TwoModeRealization p.b p.potential L T ∧
      ∀ coupling : ℝ, T ≤ coupling →
        HasGapAboveGround (magneticOperator p.b coupling (doubleWellPotential p.potential L))
          (groundEnergy p.b p.potential L coupling) := by
  obtain ⟨γ, hγ, T, hT, hground⟩ := doubleWell_parityGrounds hp cert
  refine ⟨T, hT, ?_⟩
  intro L hL
  have hcert : ∀ coupling, T ≤ coupling →
      ∃ c : ParityGroundCertificate (magneticOperator p.b coupling (doubleWellPotential p.potential L))
          true (evenEnergy p.b p.potential L coupling),
      ∃ d : ParityGroundCertificate (magneticOperator p.b coupling (doubleWellPotential p.potential L))
          false (oddEnergy p.b p.potential L coupling),
        oddEnergy p.b p.potential L coupling ≤ evenEnergy p.b p.potential L coupling + c.gap ∧
        evenEnergy p.b p.potential L coupling ≤ oddEnergy p.b p.potential L coupling + d.gap := by
    intro coupling hc
    obtain ⟨c, hE, _, hfloorE⟩ := hground coupling hc L hL true
    obtain ⟨d, hF, _, hfloorF⟩ := hground coupling hc L hL false
    have hg : 0 < γ * coupling := mul_pos hγ (hT.trans_le hc)
    refine ⟨c, d, ?_, ?_⟩
    · change parityEnergy p.b p.potential L coupling false ≤
        parityEnergy p.b p.potential L coupling true + c.gap
      rw [hfloorE]
      nlinarith only [hF, hg]
    · change parityEnergy p.b p.potential L coupling true ≤
        parityEnergy p.b p.potential L coupling false + d.gap
      rw [hfloorF]
      nlinarith only [hE, hg]
  have hv := admissiblePotential hp
  have hA (coupling : ℝ) := magnetic_realization p.b coupling (doubleWellPotential p.potential L)
    (hv.doubleWell_smooth L) (hv.doubleWell_bounded L)
  obtain ⟨B, hB⟩ := hv.doubleWell_bounded L
  refine ⟨twoModeRealization_of_parityGroundCertificates hA
    (hv.doubleWell_smooth L).continuous hB hcert, ?_⟩
  intro coupling hc
  obtain ⟨c, d, _, _⟩ := hcert coupling hc
  exact (hA coupling).ground_gap_of_parityGroundCertificates c d

theorem doubleWell_spectral_realization {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ T > 0, ∀ L : ℝ, cert.L₀ ≤ L →
      SpectralRealization p.b p.potential L T ∧
      ∀ coupling : ℝ, T ≤ coupling →
        HasGapAboveGround (magneticOperator p.b coupling (doubleWellPotential p.potential L))
          (groundEnergy p.b p.potential L coupling) := by
  obtain ⟨T, hT, hmodes⟩ := doubleWell_twoModeRealization hp cert
  exact ⟨T, hT, fun L hL => ⟨(hmodes L hL).1.toSpectralRealization, (hmodes L hL).2⟩⟩

end InfiniteZero.CuspParameters
