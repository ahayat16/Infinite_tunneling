import InfiniteZero.ActiveCrossKernelBound
import InfiniteZero.InactiveKernelBounds

/-!
# Exact-action bounds for genuine active source pairings

Only the effective supports of the two integrable sources are constrained.
The magnetic phase has norm one, and the `h²` in `sourcePairing` cancels
the `h⁻²` in the exact-action kernel bound. The constant is independent
of the sources, their amplitudes, the energy, and the positive scale `h ≤ 1`.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

/-- Either ordering of the two cusp supports has the same bound, without
an action loss or an additional power of the semiclassical parameter. -/
theorem exists_activeCrossPairing_exact_action_bound {p : CuspParameters}
    (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ h > 0, h ≤ 1 →
      ∀ F G : Wavefunction, Integrable F → Integrable G →
      ((Function.support F ⊆ tsupport p.cuspPlus ∧
          Function.support G ⊆ tsupport p.cuspMinus) ∨
        (Function.support F ⊆ tsupport p.cuspMinus ∧
          Function.support G ⊆ tsupport p.cuspPlus)) →
      ‖sourcePairing h (sourceKernel p.b L h E) F G‖ ≤
        C * Real.exp (-bridgeAction p.b E (Geometry.activeDistance p.R L) / h) *
          (∫ z : Plane, ‖F z‖) * (∫ w : Plane, ‖G w‖) := by
  obtain ⟨C, hC, hK⟩ := exists_activeCrossKernel_exact_action_upper hp hL
  refine ⟨C, hC, ?_⟩
  intro E hE h hh hh1 F G hF hG hsupport
  have hpair : ∀ z ∈ Function.support F, ∀ w ∈ Function.support G,
      (z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspMinus) ∨
        (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspPlus) := by
    intro z hz w hw
    rcases hsupport with ⟨hplus, hminus⟩ | ⟨hminus, hplus⟩
    · exact Or.inl ⟨hplus hz, hminus hw⟩
    · exact Or.inr ⟨hminus hz, hplus hw⟩
  have hEp : 0 < E := lt_of_lt_of_le (by norm_num) hE.1
  have hr : ∀ z ∈ Function.support F, ∀ w ∈ Function.support G,
      0 < ‖z + w - 2 • displacement L‖ := by
    intro z hz w hw
    have hrad := activeCross_bridge_distance_bounds hp hL (hpair z hz w hw)
    exact hrad.1.trans_le hrad.2.1
  calc
    _ ≤ h ^ 2 * (C * (h ^ 2)⁻¹ *
          Real.exp (-bridgeAction p.b E (Geometry.activeDistance p.R L) / h)) *
        (∫ z : Plane, ‖F z‖) * (∫ w : Plane, ‖G w‖) :=
      norm_sourcePairing_sourceKernel_le hp.b_pos hh hEp (by positivity) hF hG hr
        (fun z hz w hw => hK E hE h hh hh1 z w (hpair z hz w hw))
    _ = _ := by field_simp

end InfiniteZero.CuspParameters
