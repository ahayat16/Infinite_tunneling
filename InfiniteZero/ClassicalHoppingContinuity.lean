import InfiniteZero.HoppingContinuity
import InfiniteZero.Remaining

/-!
# Continuity of the actual canonical hopping with only A002 and A004

The threshold precedes every well separation. The proof compares genuine
atomic ground states up to phase, uses phase invariance of hopping and
continuity of its compactly supported integral for a fixed reference state.
No continuity of the canonical eigenfunction choice is assumed.
-/

noncomputable section
open Set
namespace InfiniteZero.CuspParameters

theorem canonicalHopping_continuous {p : CuspParameters} (hp : p.BasicConditions) :
    ∃ T > 0, ∀ L : ℝ,
      ContinuousOn (canonicalHopping p.b p.potential L) (Ici T) := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hv := admissiblePotential hp
  have hcore : ∃ C : ℝ, ∀ x, |p.core x| ≤ C := by
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    exact abs_le.mpr ⟨hx.1, hx.2.trans (by norm_num)⟩
  exact exists_canonicalHopping_continuous_of_radialData hp hRad
    (fun coupling => magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos) hcore)
    (fun coupling => magnetic_realization p.b coupling p.potential hv.smooth hv.bounded)

end InfiniteZero.CuspParameters
