import InfiniteZero.DoubleWellParityGround
import InfiniteZero.Remaining
import InfiniteZero.ParityEnergyContinuity

/-!
# Genuine parity ground states for the constructed potential

Only A002 (magnetic realization) and A004 (the radial core) are instantiated.
The full atomic gap, two-well estimates, restrictions, Schur construction,
and parity-energy identification are all proved in the preceding modules.
-/

noncomputable section
open Set
namespace InfiniteZero.CuspParameters

theorem doubleWell_parityGrounds {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ γ > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ even : Bool, ∃ c : ParityGroundCertificate
        (magneticOperator p.b coupling (doubleWellPotential p.potential L)) even
        (parityEnergy p.b p.potential L coupling even),
        parityEnergy p.b p.potential L coupling even ≤
          atomicGroundEnergy p.b p.potential coupling + γ * coupling ∧
        γ * coupling ≤ c.gap ∧
        parityEnergy p.b p.potential L coupling even + c.gap =
          atomicGroundEnergy p.b p.potential coupling + 2 * γ * coupling := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hv := admissiblePotential hp
  obtain ⟨C, hC⟩ := hv.bounded
  have hcore : ∃ C : ℝ, ∀ x, |p.core x| ≤ C := by
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    exact abs_le.mpr ⟨hx.1, hx.2.trans (by norm_num)⟩
  obtain ⟨T, hT, hground⟩ := exists_doubleWell_parityGroundCertificates_of_radialData
    hp cert hRad
    (fun coupling => magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos) hcore)
    (fun coupling => magnetic_realization p.b coupling p.potential hv.smooth ⟨C, hC⟩)
    (fun coupling L => magnetic_realization p.b coupling
      (fun x => p.potential (x + displacement L))
      (hv.smooth.comp (contDiff_id.add contDiff_const)) ⟨C, fun x => hC (x + displacement L)⟩)
    (fun coupling L => magnetic_realization p.b coupling
      (fun x => p.potential (displacement L - x))
      (hv.smooth.comp (contDiff_const.sub contDiff_id)) ⟨C, fun x => hC (displacement L - x)⟩)
    (fun coupling L => magnetic_realization p.b coupling
      (doubleWellPotential p.potential L) (hv.doubleWell_smooth L) (hv.doubleWell_bounded L))
  refine ⟨hRad.gap / 8, div_pos hRad.gap_pos (by norm_num), T, hT, ?_⟩
  intro coupling hc L hL even
  obtain ⟨c, hE, hgap, hfloor⟩ := hground coupling hc L hL even
  refine ⟨c, hE, hgap, ?_⟩
  convert hfloor using 1
  ring

theorem doubleWell_parityEnergy_continuous {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) (even : Bool) :
    ContinuousOn (fun coupling : ℝ => parityEnergy p.b p.potential L coupling even) (Ioi 0) := by
  obtain ⟨_, _, T, _, hground⟩ := doubleWell_parityGrounds hp cert
  obtain ⟨c, _, _, _⟩ := hground T le_rfl L hL even
  have hv := admissiblePotential hp
  have hA := magnetic_realization p.b T (doubleWellPotential p.potential L)
    (hv.doubleWell_smooth L) (hv.doubleWell_bounded L)
  have htest := hA.exists_normalized_parity_test_of_domain_vector
    (hv.doubleWell_smooth L).continuous even c.vector c.parity c.vector_ne_zero
  exact continuousOn_parityEnergy p.b L even hv.smooth hv.compactSupport htest

theorem doubleWell_signedSplitting_continuous {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
    ContinuousOn (signedSplitting p.b p.potential L) (Ioi 0) :=
  (doubleWell_parityEnergy_continuous hp cert hL false).sub
    (doubleWell_parityEnergy_continuous hp cert hL true)

end InfiniteZero.CuspParameters
