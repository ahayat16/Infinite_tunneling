import InfiniteZero.CanonicalOverlapDecay
import InfiniteZero.GroundSpaceAlgebra

/-!
# Canonical normalized parity trial states at one uniform threshold

The actual canonical atomic ground state supplies smoothness and mass one.
The proved overlap estimate is uniform over all separations `L ≥ 4 r₀`.
Consequently the two normalized parity trials are orthogonal and linearly
independent at a coupling threshold chosen before the separation. These
are trial states, with no double-well eigenfunction assertion.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

def canonicalParityTrialState (even : Bool) (b : ℝ) (v : Potential)
    (L coupling : ℝ) : Wavefunction :=
  normalizedParityTrialState even b L coupling (canonicalAtomicState b v coupling)

theorem canonicalParityTrialStates_properties
    {b L coupling : ℝ} {v : Potential}
    (hφ : IsAtomicGroundState b v coupling (canonicalAtomicState b v coupling))
    (hs : |canonicalOverlap b v L coupling| < 1) :
    (∀ even : Bool,
      ContDiff ℝ ∞ (canonicalParityTrialState even b v L coupling) ∧
      MemLp (canonicalParityTrialState even b v L coupling) 2 volume ∧
      mass (canonicalParityTrialState even b v L coupling) = 1 ∧
      HasParity even (canonicalParityTrialState even b v L coupling)) ∧
    waveInner (canonicalParityTrialState true b v L coupling)
      (canonicalParityTrialState false b v L coupling) = 0 ∧
    LinearIndependent ℂ ![canonicalParityTrialState true b v L coupling,
      canonicalParityTrialState false b v L coupling] := by
  have hsmall : |translatedOverlap b L coupling (canonicalAtomicState b v coupling)| < 1 := hs
  have hprops (even : Bool) :
      ContDiff ℝ ∞ (canonicalParityTrialState even b v L coupling) ∧
      MemLp (canonicalParityTrialState even b v L coupling) 2 volume ∧
      mass (canonicalParityTrialState even b v L coupling) = 1 ∧
      HasParity even (canonicalParityTrialState even b v L coupling) :=
    ⟨contDiff_normalizedParityTrialState even b L coupling hφ.1.1,
      memLp_normalizedParityTrialState even b L coupling hφ.1.2.1,
      mass_normalizedParityTrialState even b L coupling hφ.1.2.1 hφ.2 hsmall,
      normalizedParityTrialState_hasParity even b L coupling _⟩
  refine ⟨hprops, normalizedParityTrialStates_orthogonal b L coupling _, ?_⟩
  exact even_odd_linearIndependent (hprops true).2.2.2 (hprops false).2.2.2
    (wavefunction_ne_zero_of_mass_one (hprops true).2.2.1)
    (wavefunction_ne_zero_of_mass_one (hprops false).2.2.1)

namespace CuspParameters

theorem exists_canonicalParityTrialStates_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ L : ℝ, 4 * p.r₀ ≤ L →
        (∀ even : Bool,
          ContDiff ℝ ∞ (canonicalParityTrialState even p.b p.potential L coupling) ∧
          MemLp (canonicalParityTrialState even p.b p.potential L coupling) 2 volume ∧
          mass (canonicalParityTrialState even p.b p.potential L coupling) = 1 ∧
          HasParity even (canonicalParityTrialState even p.b p.potential L coupling)) ∧
        waveInner (canonicalParityTrialState true p.b p.potential L coupling)
          (canonicalParityTrialState false p.b p.potential L coupling) = 0 ∧
        LinearIndependent ℂ ![canonicalParityTrialState true p.b p.potential L coupling,
          canonicalParityTrialState false p.b p.potential L coupling] := by
  obtain ⟨Ts, hTs, hsmall⟩ :=
    exists_canonicalOverlap_uniform_small_of_radialData hp hRad hAcore hApot
      (ε := 1) zero_lt_one
  obtain ⟨C, _hC, d, _hd, Tg, _hTg, hground⟩ :=
    exists_canonicalAtomicState_agmon_tail_of_radialData hp hRad hAcore hApot
  refine ⟨max Ts Tg, hTs.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL
  exact canonicalParityTrialStates_properties
    (hground coupling ((le_max_right _ _).trans hc)).1
    (hsmall coupling ((le_max_left _ _).trans hc) L hL)

end CuspParameters
end InfiniteZero
