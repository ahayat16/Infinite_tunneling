import InfiniteZero.ParityDoubletRealization
import InfiniteZero.ConstructedGlobalMinmax

/-!
# Full two-mode spectral realization for the explicit double well

The constructed parity ground certificates imply both global minmax
identifications, exact normalized physical modes and a positive gap above
the entire ground eigenspace, also at a crossing. The threshold precedes L.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem exists_doubleWell_twoModeRealization_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ T > 0, ∀ L : ℝ, cert.L₀ ≤ L →
      TwoModeRealization p.b p.potential L T ∧
      ∀ coupling : ℝ, T ≤ coupling →
        HasGapAboveGround (magneticOperator p.b coupling (doubleWellPotential p.potential L))
          (groundEnergy p.b p.potential L coupling) := by
  obtain ⟨T, hT, hground⟩ := exists_doubleWell_parityGroundCertificates_of_radialData
    hp cert hRad hAcore hApot hAleft hAright hAdouble
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
    have hg : 0 < hRad.gap / 8 * coupling :=
      mul_pos (div_pos hRad.gap_pos (by norm_num)) (hT.trans_le hc)
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
  obtain ⟨B, hB⟩ := hv.doubleWell_bounded L
  refine ⟨twoModeRealization_of_parityGroundCertificates (fun coupling => hAdouble coupling L)
    (hv.doubleWell_smooth L).continuous hB hcert, ?_⟩
  intro coupling hc
  obtain ⟨c, d, _, _⟩ := hcert coupling hc
  exact (hAdouble coupling L).ground_gap_of_parityGroundCertificates c d

end InfiniteZero.CuspParameters
