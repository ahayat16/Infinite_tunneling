import InfiniteZero.Remaining
import InfiniteZero.CanonicalOverlapDecay

/-!
# Canonical overlap decay from the documented classical atomic inputs

Only A002 (operator realization) and A004 (radial spectral data) are
instantiated here. The full atomic state, its exterior decay, and the
geometric overlap bound are proved in the conditional modules. The constants
precede both the coupling and every separation at least `4 * p.r₀`.
-/

noncomputable section

open Filter
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem canonicalOverlap_decay {p : CuspParameters} (hp : p.BasicConditions) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ L : ℝ, 4 * p.r₀ ≤ L →
        |canonicalOverlap p.b p.potential L coupling| ≤
          C / coupling * Real.exp (-d * coupling) := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  apply exists_canonicalOverlap_bound_of_radialData hp hRad
  · intro coupling
    apply magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  · intro coupling
    exact magnetic_realization p.b coupling p.potential
      (admissiblePotential hp).smooth (admissiblePotential hp).bounded

/-- The usual geometric separation implies the radius required by the
overlap estimate, since the fixed construction satisfies `8 * p.r₀ < p.R`. -/
theorem canonicalOverlap_tendsto {p : CuspParameters} (hp : p.BasicConditions)
    {L : ℝ} (hL : p.R < 2 * L) :
    Tendsto (canonicalOverlap p.b p.potential L) atTop (𝓝 0) := by
  obtain ⟨C, _, d, hd, T, _, hbound⟩ := canonicalOverlap_decay hp
  have hL' : 4 * p.r₀ ≤ L := by linarith [hp.radius_large]
  apply squeeze_zero_norm' _ (tendsto_overlap_decay C hd)
  filter_upwards [eventually_ge_atTop T] with coupling hc
  simpa only [Real.norm_eq_abs] using hbound coupling hc L hL'

end InfiniteZero.CuspParameters
