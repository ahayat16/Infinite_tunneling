import InfiniteZero.ParityGlobalMinmax
import InfiniteZero.DoubleWellParityGround
import InfiniteZero.OperatorMain

/-!
# The two actual global minmax values for the constructed potential

The sector certificates used below were constructed from the physical
atomic trials and the two-well coercivity estimate. No global minmax
identification or two-well spectral input is assumed.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem exists_doubleWell_global_minmax_of_radialData
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
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      groundEnergy p.b p.potential L coupling =
        min (evenEnergy p.b p.potential L coupling) (oddEnergy p.b p.potential L coupling) ∧
      secondEnergy p.b p.potential L coupling =
        max (evenEnergy p.b p.potential L coupling) (oddEnergy p.b p.potential L coupling) := by
  obtain ⟨T, hT, hground⟩ := exists_doubleWell_parityGroundCertificates_of_radialData
    hp cert hRad hAcore hApot hAleft hAright hAdouble
  refine ⟨T, hT, ?_⟩
  intro coupling hc L hL
  obtain ⟨c, hE, _, hfloorE⟩ := hground coupling hc L hL true
  obtain ⟨d, hF, _, hfloorF⟩ := hground coupling hc L hL false
  have hA := hAdouble coupling L
  have hv := admissiblePotential hp
  obtain ⟨B, hB⟩ := hv.doubleWell_bounded L
  have hg : 0 < hRad.gap / 8 * coupling :=
    mul_pos (div_pos hRad.gap_pos (by norm_num)) (hT.trans_le hc)
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
