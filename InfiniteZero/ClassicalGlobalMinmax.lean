import InfiniteZero.ConstructedGlobalMinmax
import InfiniteZero.ClassicalDoubleWellParityGround

/-!
# Global minmax identification with only the classical radial inputs

A002 and A004 are the only admitted dependencies. The two sector
certificates, the global form bounds and both minmax identifications
are proved, with the threshold chosen before the separation.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem doubleWell_global_minmax {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      groundEnergy p.b p.potential L coupling =
        min (evenEnergy p.b p.potential L coupling) (oddEnergy p.b p.potential L coupling) ∧
      secondEnergy p.b p.potential L coupling =
        max (evenEnergy p.b p.potential L coupling) (oddEnergy p.b p.potential L coupling) := by
  obtain ⟨γ, hγ, T, hT, hground⟩ := doubleWell_parityGrounds hp cert
  refine ⟨T, hT, ?_⟩
  intro coupling hc L hL
  obtain ⟨c, hE, _, hfloorE⟩ := hground coupling hc L hL true
  obtain ⟨d, hF, _, hfloorF⟩ := hground coupling hc L hL false
  have hv := admissiblePotential hp
  have hA := magnetic_realization p.b coupling (doubleWellPotential p.potential L)
    (hv.doubleWell_smooth L) (hv.doubleWell_bounded L)
  obtain ⟨B, hB⟩ := hv.doubleWell_bounded L
  have hg : 0 < γ * coupling := mul_pos hγ (hT.trans_le hc)
  refine ⟨hA.groundEnergy_eq_min_of_parityGroundCertificates c d,
    hA.secondEnergy_eq_max_of_parityGroundCertificates (hv.doubleWell_smooth L).continuous
      hB c d ?_ ?_⟩
  · change parityEnergy p.b p.potential L coupling false ≤
      parityEnergy p.b p.potential L coupling true + c.gap
    rw [hfloorE]
    nlinarith only [hF, hg]
  · change parityEnergy p.b p.potential L coupling true ≤
      parityEnergy p.b p.potential L coupling false + d.gap
    rw [hfloorF]
    nlinarith only [hE, hg]

end InfiniteZero.CuspParameters
