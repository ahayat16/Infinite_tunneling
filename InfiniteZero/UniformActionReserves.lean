import InfiniteZero.ActionReserves
import InfiniteZero.BridgeActionEnergy

/-!
# A separation threshold uniform in the energy parameters

The quadratic lower bound for an action increment is independent of the
positive incoming energy. The reference energy can range in any fixed bounded
positive interval. Thus a single large separation works for all those energies,
without changing the previously fixed potential or cusp profile.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

def uniformReserveLower (b R δ m Emax L : ℝ) : ℝ :=
  b * δ / 2 * Geometry.activeDistance R L + b * δ ^ 2 / 4 -
    m * bridgeAction b Emax R

theorem uniformReserveLower_le_channelReserve {b R δ m E E₀ Emax L : ℝ}
    (hb : 0 < b) (hR : 0 < R) (hδ : 0 < δ) (hm : 0 ≤ m)
    (hE : 0 < E) (hE₀ : 0 < E₀) (hEmax : E₀ ≤ Emax) (hL : R / 2 ≤ L) :
    uniformReserveLower b R δ m Emax L ≤ channelReserve b R δ m E E₀ L := by
  have hD : 0 ≤ Geometry.activeDistance R L := by
    dsimp [Geometry.activeDistance]
    linarith
  have hinc := actionIncrement_ge_affine hb hE hδ hD
  have href := mul_le_mul_of_nonneg_left (bridgeAction_energy_le hb.ne' hR hE₀ hEmax) hm
  dsimp only [uniformReserveLower, channelReserve]
  linarith

theorem tendsto_uniformReserveLower {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (R m Emax : ℝ) : Tendsto (uniformReserveLower b R δ m Emax) atTop atTop := by
  have hlinear : Tendsto (fun L : ℝ => b * δ * L +
      (-b * δ * R / 2 + b * δ ^ 2 / 4 - m * bridgeAction b Emax R)) atTop atTop :=
    tendsto_atTop_add_const_right atTop _
      (tendsto_id.const_mul_atTop (mul_pos hb hδ))
  convert hlinear using 1
  funext L
  dsimp [uniformReserveLower, Geometry.activeDistance]
  ring

/-- The incoming energy is arbitrary positive; only the reference energy needs
an upper bound. This is stronger than a small window around `(1,1)`. -/
theorem exists_uniform_channelReserve_threshold {b R δ m : ℝ}
    (hb : 0 < b) (hR : 0 < R) (hδ : 0 < δ) (hm : 0 ≤ m)
    (Emax margin lower : ℝ) :
    ∃ L₀ : ℝ, lower < L₀ ∧ R / 2 < L₀ ∧
      ∀ L, L₀ ≤ L → ∀ E E₀, 0 < E → 0 < E₀ → E₀ ≤ Emax →
        margin ≤ channelReserve b R δ m E E₀ L := by
  have hev := (tendsto_uniformReserveLower hb hδ R m Emax).eventually
    (eventually_ge_atTop margin)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  let L₀ := max T (max lower (R / 2)) + 1
  have hTL : T ≤ L₀ := by
    dsimp [L₀]
    linarith [le_max_left T (max lower (R / 2))]
  have hlo : lower < L₀ := by
    dsimp [L₀]
    linarith [le_max_right T (max lower (R / 2)), le_max_left lower (R / 2)]
  have hRlo : R / 2 < L₀ := by
    dsimp [L₀]
    linarith [le_max_right T (max lower (R / 2)), le_max_right lower (R / 2)]
  refine ⟨L₀, hlo, hRlo, ?_⟩
  intro L hL E E₀ hE hE₀ hEmax
  exact (hT L (hTL.trans hL)).trans
    (uniformReserveLower_le_channelReserve hb hR hδ hm hE hE₀ hEmax (hRlo.le.trans hL))

end InfiniteZero
