import InfiniteZero.UniformActionReserves
import InfiniteZero.GeometryAction
import InfiniteZero.ConstructionExistence
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A proved separation choice after the potential is fixed

This certificate covers support separation and the pointwise action reserves.
It does not assert any spectral or source estimate. Its existence is proved
from BasicConditions and used by the final construction.
The energy window is obtained from a uniform quadratic bound, without shrinking
or otherwise changing the single-well potential.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

def hopMargin (p : CuspParameters) : ℝ := p.b * p.R ^ 2 / 64

def coreCuspIncrement (p : CuspParameters) : ℝ := p.R / 2 - p.r₀

def coreCoreIncrement (p : CuspParameters) : ℝ := p.R - 2 * p.r₀

theorem hopMargin_pos {p : CuspParameters} (h : p.BasicConditions) : 0 < p.hopMargin := by
  unfold hopMargin
  have := h.b_pos
  have := h.radius_pos
  positivity

theorem coreCuspIncrement_pos {p : CuspParameters} (h : p.BasicConditions) :
    0 < p.coreCuspIncrement := by
  dsimp [coreCuspIncrement]
  linarith [h.radius_large, h.r₀_pos]

theorem coreCoreIncrement_pos {p : CuspParameters} (h : p.BasicConditions) :
    0 < p.coreCoreIncrement := by
  dsimp [coreCoreIncrement]
  linarith [h.radius_large, h.r₀_pos]

/-- Geometric and real-action output only; no claim about eigenfunctions or
the hopping integral is encoded in this certificate. -/
structure SeparationCertificate (p : CuspParameters) where
  supportRadius : ℝ
  supportRadius_pos : 0 < supportRadius
  support_bound : ∀ x ∈ tsupport p.potential, ‖x‖ ≤ supportRadius
  L₀ : ℝ
  separation : max supportRadius p.R < L₀
  core_cusp_reserve : ∀ L, L₀ ≤ L → ∀ E E₀, 0 < E → 0 < E₀ → E₀ ≤ 2 →
    32 * p.hopMargin ≤ channelReserve p.b p.R p.coreCuspIncrement 1 E E₀ L
  core_core_reserve : ∀ L, L₀ ≤ L → ∀ E E₀, 0 < E → 0 < E₀ → E₀ ≤ 2 →
    32 * p.hopMargin ≤ channelReserve p.b p.R p.coreCoreIncrement 2 E E₀ L
  same_cusp_reserve : ∀ L, L₀ ≤ L → ∀ E, 0 < E →
    48 * p.hopMargin ≤ bridgeAction p.b E
      (Geometry.length (Geometry.bridge L (Geometry.tipPlus p.R) (Geometry.tipPlus p.R))) -
        bridgeAction p.b E (Geometry.activeDistance p.R L)

/-- The quantifier order is `∀ fixed p, ∃ L₀, ∀ later L, ∀ energies`. -/
theorem exists_separationCertificate {p : CuspParameters} (h : p.BasicConditions) :
    Nonempty (SeparationCertificate p) := by
  obtain ⟨a, ha, hbound⟩ := (potential_hasCompactSupport h).isBounded.exists_pos_norm_le
  obtain ⟨Lcp, hcp, _, hcp_res⟩ := exists_uniform_channelReserve_threshold
    h.b_pos h.radius_pos (coreCuspIncrement_pos h) (by norm_num : (0 : ℝ) ≤ 1)
    2 (32 * p.hopMargin) (max a p.R)
  obtain ⟨Lcc, hcc, _, hcc_res⟩ := exists_uniform_channelReserve_threshold
    h.b_pos h.radius_pos (coreCoreIncrement_pos h) (by norm_num : (0 : ℝ) ≤ 2)
    2 (32 * p.hopMargin) (max a p.R)
  let L₀ := max Lcp Lcc
  have hcpL : Lcp ≤ L₀ := le_max_left _ _
  have hccL : Lcc ≤ L₀ := le_max_right _ _
  have hsep : max a p.R < L₀ := hcp.trans_le hcpL
  refine ⟨⟨a, ha, hbound, L₀, hsep, ?_, ?_, ?_⟩⟩
  · intro L hL
    exact hcp_res L (hcpL.trans hL)
  · intro L hL
    exact hcc_res L (hccL.trans hL)
  · intro L hL E hE
    have hRL : p.R < L := (lt_of_le_of_lt (le_max_right a p.R) hsep).trans_le hL
    have htwo : p.R < 2 * L := by linarith [h.radius_pos]
    have hmargin := Geometry.same_cusp_action_gap_ge h.b_pos hE h.radius_pos htwo
    convert hmargin using 1
    dsimp [hopMargin]
    ring

end InfiniteZero.CuspParameters
