import InfiniteZero.ComplexCuspGeometry
import InfiniteZero.LogFlatActiveTruncation

/-! The moving normal window lies in the common analytic radius domain and
in the constant part of the actual potential cutoff. The cutoff itself is
not asserted to have any holomorphic continuation. -/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

namespace Geometry

theorem eventually_activeWindow_mem_complexCuspRadiusDomain
    {R L tStar : ℝ} (hR : 0 < R) (hL : R < 2 * L) (s₀ : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ s₀ → |r| ≤ s₀ →
      ∀ t u : ℂ, ‖t‖ ≤ logFlatActiveWindow tStar h →
        ‖u‖ ≤ logFlatActiveWindow tStar h →
        (t, u) ∈ complexCuspRadiusDomain R L s r := by
  obtain ⟨δ, hδ, hbidisc⟩ := exists_uniform_complexCusp_bidisc hR hL s₀
  filter_upwards [(tendsto_logFlatActiveWindow tStar).eventually (gt_mem_nhds hδ)] with h hh
  intro s r hs hr t u ht hu
  exact hbidisc s r hs hr t u (ht.trans_lt hh) (hu.trans_lt hh)

end Geometry

namespace CuspParameters

theorem eventually_cutoff_one_on_activeWindow {p : CuspParameters} (hp : p.BasicConditions) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ t ∈ Icc 0 (logFlatActiveWindow p.tStar h), p.χa t = 1 := by
  obtain ⟨t₂, ht₂, _, hone⟩ := hp.χa_one
  filter_upwards [(tendsto_logFlatActiveWindow p.tStar).eventually (gt_mem_nhds ht₂)] with h hh
  intro t ht
  exact hone t ⟨ht.1, ht.2.trans hh.le⟩

theorem eventually_activeWindow_local {p : CuspParameters} (hp : p.BasicConditions)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (0 < logFlatActiveWindow p.tStar h ∧ logFlatActiveWindow p.tStar h < p.t₀) ∧
      (∀ t ∈ Icc 0 (logFlatActiveWindow p.tStar h), p.χa t = 1) ∧
      (∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ → ∀ t u : ℂ,
        ‖t‖ ≤ logFlatActiveWindow p.tStar h → ‖u‖ ≤ logFlatActiveWindow p.tStar h →
        (t, u) ∈ Geometry.complexCuspRadiusDomain p.R L s r) := by
  filter_upwards [(tendsto_logFlatActiveWindow p.tStar).eventually (gt_mem_nhds hp.t₀_pos),
    eventually_cutoff_one_on_activeWindow hp,
    Geometry.eventually_activeWindow_mem_complexCuspRadiusDomain
      (tStar := p.tStar) hp.radius_pos hL p.s₀] with h hh hcut hgeo
  exact ⟨⟨logFlatActiveWindow_pos (hp.t₀_pos.trans hp.t₀_lt) h, hh⟩, hcut, hgeo⟩

end CuspParameters

end InfiniteZero
