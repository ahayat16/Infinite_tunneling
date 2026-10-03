import InfiniteZero.AtomicGroundEnergyBounds
import InfiniteZero.Main

/-!
# The actual atomic state and source representation at large coupling

These are consequences of the radial spectral input and the universal
operator/resolvent interfaces. They contain no active-cell asymptotic,
source decay estimate, double-well reduction, or tunneling error bound.
The same coupling threshold works for all separations in this module.
-/

noncomputable section
namespace InfiniteZero

structure AtomicSourceFacts (p : CuspParameters) (coupling : ℝ) : Prop where
  coupling_pos : 0 < coupling
  ground : IsAtomicGroundState p.b p.potential coupling
    (canonicalAtomicState p.b p.potential coupling)
  simple : AtomicGroundSimple p.b p.potential coupling
  gap : HasGapAboveGround (magneticOperator p.b coupling p.potential)
    (atomicGroundEnergy p.b p.potential coupling)
  energy_lower : (1 / 2 : ℝ) ≤ scaledAtomicEnergy p coupling
  energy_upper : scaledAtomicEnergy p coupling ≤ 1
  representation : ∀ L : ℝ,
    RightResolventRepresentation p.b p.potential L coupling (scaledAtomicEnergy p coupling)
      (canonicalAtomicState p.b p.potential coupling)
  cells_integrable : ∀ L : ℝ, p.R < 2 * L →
    CellsIntegrable p L coupling⁻¹ (scaledAtomicEnergy p coupling)
      (canonicalAtomicState p.b p.potential coupling)

theorem AtomicSourceFacts.energy_pos {p : CuspParameters} {coupling : ℝ}
    (h : AtomicSourceFacts p coupling) : 0 < scaledAtomicEnergy p coupling :=
  lt_of_lt_of_le (by norm_num) h.energy_lower

theorem AtomicSourceFacts.hopping_eq_source {p : CuspParameters} {coupling L : ℝ}
    (h : AtomicSourceFacts p coupling) (hL : p.R < 2 * L) :
    canonicalHopping p.b p.potential L coupling = canonicalTotalSourcePairing p L coupling :=
  canonicalHopping_eq_source_of_resolvent p L coupling (h.representation L)
    (h.cells_integrable L hL)

theorem AtomicSourceFacts.hopping_real {p : CuspParameters} {coupling L : ℝ}
    (h : AtomicSourceFacts p coupling) (hL : p.R < 2 * L) :
    (canonicalHopping p.b p.potential L coupling).im = 0 :=
  canonicalHopping_real_of_resolvent p L coupling (h.representation L)
    (h.cells_integrable L hL)

theorem CuspParameters.exists_atomicSourceFacts_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hKernel : HasPositiveLandauResolvent p.b) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → AtomicSourceFacts p coupling := by
  obtain ⟨Tg, hTg, hg⟩ := CuspParameters.eventual_atomicGround_properties_of_radialData
    hp hRad hAcore hApot
  obtain ⟨Te, _, he⟩ := CuspParameters.exists_scaledAtomicEnergy_pos_of_radialData
    hp hRad hAcore hApot
  refine ⟨max Tg Te, hTg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcg : Tg ≤ coupling := (le_max_left Tg Te).trans hc
  have hce : Te ≤ coupling := (le_max_right Tg Te).trans hc
  have hcpos : 0 < coupling := hTg.trans_le hcg
  obtain ⟨hex, hs, hgap, _⟩ := hg coupling hcg
  obtain ⟨helower, hepos, heupper⟩ := he coupling hce
  have hground := canonicalAtomicState_spec p.b p.potential coupling hex
  refine ⟨hcpos, hground, hs, hgap, helower, heupper, ?_, ?_⟩
  · intro L
    exact rightResolventRepresentation_of_freeLandauResolventKernel
      (hKernel coupling (scaledAtomicEnergy p coupling) hcpos hepos)
      (CuspParameters.potential_contDiff hp) (CuspParameters.potential_hasCompactSupport hp)
      hground hcpos rfl L
  · intro L hL
    exact cellsIntegrable_of_continuous hp hL (inv_pos.mpr hcpos) hepos
      hground.1.1.continuous

end InfiniteZero
