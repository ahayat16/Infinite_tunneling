import InfiniteZero.DoubleWellOperatorCoercivity
import InfiniteZero.AtomicTranslatedOverlap
import InfiniteZero.ParityTrialL2

/-!
# Coercivity on the complement of the physical parity trial

Inside a fixed parity sector, orthogonality to the normalized signed sum
of the two translated atomic states implies orthogonality to each state.
The actual two-well complement estimate therefore supplies an order-coupling
gap on this sectorial complement. Uniform overlap decay provides the
nonzero normalization, with one threshold before the separation is chosen.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero.CuspParameters

theorem exists_parityTrial_complement_gap_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ even : Bool, ∀ q : L2Space,
        Represents q (normalizedParityTrialState even p.b L coupling φ) →
      ∀ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
        HasL2Parity even (u : L2Space) → inner ℂ q (u : L2Space) = 0 →
        (atomicGroundEnergy p.b p.potential coupling + hRad.gap / 4 * coupling) *
          ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator p.b coupling (doubleWellPotential p.potential L) u)).re := by
  obtain ⟨T, hT, hgap⟩ := exists_doubleWell_operator_complement_gap_of_radialData
    hp cert hRad hAcore hApot hAdouble
  obtain ⟨N, _, hsmall⟩ := exists_translatedOverlap_uniform_small_of_radialData
    hp hRad hAcore hApot (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T N, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcT := (le_max_left T N).trans hc
  have hcN := (le_max_right T N).trans hc
  refine ⟨(hgap coupling hcT).1, ?_⟩
  intro L hL φ hφ even q hq u hu horth
  have hRL : p.R < L :=
    (lt_of_le_of_lt (le_max_right _ _) cert.separation).trans_le hL
  have hrL : 4 * p.r₀ ≤ L := by linarith [hp.radius_large, hp.r₀_pos]
  have hs := hsmall coupling hcN L hrL φ hφ
  have hleft := memLp_leftState p.b L coupling hφ.1.2.1
  let vL : L2Space := hleft.toLp (leftState p.b L coupling φ)
  have hvL : Represents vL (leftState p.b L coupling φ) := represents_toLp hleft
  have hvR : Represents (l2Inversion vL) (rightState p.b L coupling φ) := hvL.inversion
  obtain ⟨huL, huR⟩ := normalizedParityTrial_complement_orthogonal
    even hvL hvR hq hs hu horth
  exact (hgap coupling hcT).2 L hL φ hφ vL (l2Inversion vL) hvL hvR u huL huR

end InfiniteZero.CuspParameters
