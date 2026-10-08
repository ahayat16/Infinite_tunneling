import InfiniteZero.BridgeAction
import InfiniteZero.Geometry
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Increasing and unbounded action reserves

The displacement of the wells is chosen after the single-well parameters.
For every fixed positive radial increment, the corresponding action gain
increases with the bridge length and tends to infinity. This is the reserve
used to suppress the core--cusp and core--core channels.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

def actionIncrement (b E δ D : ℝ) : ℝ :=
  bridgeAction b E (D + δ) - bridgeAction b E D

theorem hasDerivAt_actionIncrement {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (δ D : ℝ) :
    HasDerivAt (actionIncrement b E δ)
      (deriv (bridgeAction b E) (D + δ) - deriv (bridgeAction b E) D) D := by
  simpa [actionIncrement] using
    ((((differentiable_bridgeAction hb hE (D + δ)).hasDerivAt).comp D
    ((hasDerivAt_id D).add_const δ)).sub
    (differentiable_bridgeAction hb hE D).hasDerivAt)

theorem strictMonoOn_actionIncrement {b E δ : ℝ} (hb : b ≠ 0) (hE : 0 < E)
    (hδ : 0 < δ) : StrictMonoOn (actionIncrement b E δ) (Ici 0) := by
  have hmono := (strictConvexOn_bridgeAction hb hE).strictMonoOn_deriv
    (fun x _ => differentiable_bridgeAction hb hE x)
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun x _ => (hasDerivAt_actionIncrement hb hE δ x).continuousAt.continuousWithinAt)
  intro D hD
  rw [(hasDerivAt_actionIncrement hb hE δ D).deriv]
  have hD0 : 0 ≤ D := interior_subset hD
  exact sub_pos.mpr (hmono hD0 (show 0 ≤ D + δ by linarith) (by linarith))

theorem actionIncrement_ge_affine {b E δ D : ℝ} (hb : 0 < b) (hE : 0 < E)
    (hδ : 0 < δ) (hD : 0 ≤ D) :
    b * δ / 2 * D + b * δ ^ 2 / 4 ≤ actionIncrement b E δ D := by
  have hg := bridgeAction_sub_ge_quadratic hb hE hD (show D ≤ D + δ by linarith)
  dsimp [actionIncrement]
  nlinarith only [hg]

theorem tendsto_actionIncrement {b E δ : ℝ} (hb : 0 < b) (hE : 0 < E)
    (hδ : 0 < δ) : Tendsto (actionIncrement b E δ) atTop atTop := by
  have hlin : Tendsto (fun D : ℝ => b * δ / 2 * D + b * δ ^ 2 / 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop _
      (tendsto_id.const_mul_atTop (by positivity : 0 < b * δ / 2))
  apply tendsto_atTop_mono' atTop _ hlin
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
  exact actionIncrement_ge_affine hb hE hδ hD

/-- A channel reserve, with incoming and reference energies kept separate. -/
def channelReserve (b R δ m E E₀ L : ℝ) : ℝ :=
  actionIncrement b E δ (Geometry.activeDistance R L) - m * bridgeAction b E₀ R

theorem strictMonoOn_channelReserve {b E δ : ℝ} (hb : b ≠ 0) (hE : 0 < E)
    (hδ : 0 < δ) (R m E₀ : ℝ) :
    StrictMonoOn (channelReserve b R δ m E E₀) (Ici (R / 2)) := by
  intro L hL L' hL' hLL'
  change actionIncrement b E δ (Geometry.activeDistance R L) - _ <
    actionIncrement b E δ (Geometry.activeDistance R L') - _
  apply sub_lt_sub_right
  apply strictMonoOn_actionIncrement hb hE hδ
  · change 0 ≤ 2 * L - R
    change R / 2 ≤ L at hL
    linarith
  · change 0 ≤ 2 * L' - R
    change R / 2 ≤ L' at hL'
    linarith
  · dsimp [Geometry.activeDistance]
    linarith

theorem tendsto_channelReserve {b E δ : ℝ} (hb : 0 < b) (hE : 0 < E)
    (hδ : 0 < δ) (R m E₀ : ℝ) :
    Tendsto (channelReserve b R δ m E E₀) atTop atTop := by
  have hD : Tendsto (Geometry.activeDistance R) atTop atTop := by
    simpa only [Geometry.activeDistance, sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-R)
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have h := (tendsto_actionIncrement hb hE hδ).comp hD
  simpa only [channelReserve, sub_eq_add_neg, Function.comp_apply, neg_mul] using
    tendsto_atTop_add_const_right atTop (-m * bridgeAction b E₀ R) h

end InfiniteZero
