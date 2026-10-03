import InfiniteZero.ConstructionCuspBounds
import InfiniteZero.CuspWeight
import InfiniteZero.AtomicPerturbationDomain

/-!
# A uniform radial action gain after applying the exact cusp weight

For energies in `[1/2,1]`, outgoing cusp geometry gains at least `t/8`
in radial action. A weight strength at most `1/16` leaves a gain of
`t/16`. The estimates hold on the closed supports; positivity and the
strict upper normal bound are recorded separately on the open supports.
All radial bounds use the fixed geometric `cuspSupportRadius`.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

theorem cuspMinus_support_normal_bounds (p : CuspParameters) {x : Plane}
    (hx : x ∈ Function.support p.cuspMinus) :
    0 < p.normalCoordinate (reflection x) ∧
      p.normalCoordinate (reflection x) < p.t₀ :=
  cuspPlus_support_normal_bounds p (x := reflection x) hx

/-- The whole closed upper support lies in one fixed positive annulus. -/
theorem cuspPlus_tsupport_norm_bounds {p : CuspParameters} (hp : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    ‖x‖ ∈ Icc p.R p.cuspSupportRadius := by
  have ht := (cuspPlus_tsupport_subset_quadratic p hx).1
  have hrad := cuspPlus_tsupport_radial hp hx
  have hupper : tsupport p.cuspPlus ⊆ {y : Plane | ‖y‖ ≤ p.cuspSupportRadius} :=
    closure_minimal (fun _ hy => cuspPlus_norm_bound hp hy)
      (isClosed_le continuous_norm continuous_const)
  exact ⟨by linarith, hupper hx⟩

theorem cuspMinus_tsupport_norm_bounds {p : CuspParameters} (hp : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspMinus) :
    ‖x‖ ∈ Icc p.R p.cuspSupportRadius := by
  have href : reflection x ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
  simpa only [norm_reflection] using cuspPlus_tsupport_norm_bounds hp href

theorem cuspPlus_tsupport_outside_core {p : CuspParameters} (hp : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) : p.r₀ < ‖x‖ := by
  have hrad := (cuspPlus_tsupport_norm_bounds hp hx).1
  linarith [hp.radius_large, hp.r₀_pos]

theorem cuspMinus_tsupport_outside_core {p : CuspParameters} (hp : p.BasicConditions)
    {x : Plane} (hx : x ∈ tsupport p.cuspMinus) : p.r₀ < ‖x‖ := by
  have hrad := (cuspMinus_tsupport_norm_bounds hp hx).1
  linarith [hp.radius_large, hp.r₀_pos]

theorem atomicPerturbation_support_subset_cusps (p : CuspParameters) :
    Function.support p.atomicPerturbation ⊆
      Function.support p.cuspPlus ∪ Function.support p.cuspMinus := by
  intro x hx
  by_contra hn
  have hp : p.cuspPlus x = 0 := by
    by_contra h
    exact hn (Or.inl h)
  have hm : p.cuspMinus x = 0 := by
    by_contra h
    exact hn (Or.inr h)
  exact hx (by simp [atomicPerturbation, potential, hp, hm])

theorem atomicPerturbation_tsupport_subset_cusps (p : CuspParameters) :
    tsupport p.atomicPerturbation ⊆ tsupport p.cuspPlus ∪ tsupport p.cuspMinus := by
  apply closure_minimal
  · intro x hx
    rcases atomicPerturbation_support_subset_cusps p hx with hp | hm
    · exact Or.inl (subset_tsupport _ hp)
    · exact Or.inr (subset_tsupport _ hm)
  · exact (isClosed_tsupport _).union (isClosed_tsupport _)

/-- The radius interval is independent of the energy, coupling and weight. -/
theorem atomicPerturbation_tsupport_norm_bounds {p : CuspParameters}
    (hp : p.BasicConditions) {x : Plane} (hx : x ∈ tsupport p.atomicPerturbation) :
    ‖x‖ ∈ Icc p.R p.cuspSupportRadius := by
  rcases atomicPerturbation_tsupport_subset_cusps p hx with hplus | hminus
  · exact cuspPlus_tsupport_norm_bounds hp hplus
  · exact cuspMinus_tsupport_norm_bounds hp hminus

theorem cuspPlus_tsupport_action_gain_eighth {p : CuspParameters}
    (hp : p.BasicConditions) {E : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1)
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    bridgeAction p.b E p.R + p.normalCoordinate x / 8 ≤ bridgeAction p.b E ‖x‖ := by
  have hEpos : 0 < E := lt_of_lt_of_le (by norm_num) hE.1
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt E := by
    nlinarith [Real.sq_sqrt hEpos.le, Real.sqrt_nonneg E, hE.1]
  have ht := (cuspPlus_tsupport_subset_quadratic p hx).1
  have hmul := mul_le_mul_of_nonneg_right hsqrt ht
  have hgain := cuspPlus_tsupport_radial_action_gain hp hEpos hx
  nlinarith

theorem cuspMinus_tsupport_action_gain_eighth {p : CuspParameters}
    (hp : p.BasicConditions) {E : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1)
    {x : Plane} (hx : x ∈ tsupport p.cuspMinus) :
    bridgeAction p.b E p.R + p.normalCoordinate (reflection x) / 8 ≤
      bridgeAction p.b E ‖x‖ := by
  have href : reflection x ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
  simpa only [norm_reflection] using cuspPlus_tsupport_action_gain_eighth hp hE href

namespace CuspWeightCutoffs

variable {p : CuspParameters} (χ : CuspWeightCutoffs p)

theorem cuspPlus_weighted_action_gain (hp : p.BasicConditions)
    {E κ : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1) (hκ : κ ∈ Icc (0 : ℝ) (1 / 16))
    {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    κ * χ.weight x - (bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R) ≤
      -p.normalCoordinate x / 16 := by
  rw [χ.weight_eq_normal_on_plus hx]
  have ht := (cuspPlus_tsupport_subset_quadratic p hx).1
  have hmul := mul_le_mul_of_nonneg_right hκ.2 ht
  have hgain := cuspPlus_tsupport_action_gain_eighth hp hE hx
  linarith

theorem cuspMinus_weighted_action_gain (hp : p.BasicConditions)
    {E κ : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1) (hκ : κ ∈ Icc (0 : ℝ) (1 / 16))
    {x : Plane} (hx : x ∈ tsupport p.cuspMinus) :
    κ * χ.weight x - (bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R) ≤
      -p.normalCoordinate (reflection x) / 16 := by
  rw [χ.weight_eq_normal_on_minus hx]
  have href : reflection x ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
  have ht := (cuspPlus_tsupport_subset_quadratic p href).1
  have hmul := mul_le_mul_of_nonneg_right hκ.2 ht
  have hgain := cuspMinus_tsupport_action_gain_eighth hp hE hx
  linarith

/-- A single weighted inequality on the complete closed perturbation support. -/
theorem atomicPerturbation_weighted_action_gain (hp : p.BasicConditions)
    {E κ : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1) (hκ : κ ∈ Icc (0 : ℝ) (1 / 16))
    {x : Plane} (hx : x ∈ tsupport p.atomicPerturbation) :
    κ * χ.weight x - (bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R) ≤
      -χ.weight x / 16 := by
  rcases atomicPerturbation_tsupport_subset_cusps p hx with hplus | hminus
  · simpa only [χ.weight_eq_normal_on_plus hplus] using
      χ.cuspPlus_weighted_action_gain hp hE hκ hplus
  · simpa only [χ.weight_eq_normal_on_minus hminus] using
      χ.cuspMinus_weighted_action_gain hp hE hκ hminus

/-- Open-support data used to insert the real exterior kernel and integrate
in the upper normal coordinate. -/
theorem cuspPlus_support_weighted_action_bounds (hp : p.BasicConditions)
    {E κ : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1) (hκ : κ ∈ Icc (0 : ℝ) (1 / 16))
    {x : Plane} (hx : x ∈ Function.support p.cuspPlus) :
    p.normalCoordinate x ∈ Ioo 0 p.t₀ ∧ p.r₀ < ‖x‖ ∧
      ‖x‖ ∈ Icc p.R p.cuspSupportRadius ∧
      bridgeAction p.b E p.R + p.normalCoordinate x / 8 ≤ bridgeAction p.b E ‖x‖ ∧
      κ * χ.weight x - (bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R) ≤
        -p.normalCoordinate x / 16 := by
  have hclosed := subset_tsupport p.cuspPlus hx
  exact ⟨cuspPlus_support_normal_bounds p hx, cuspPlus_tsupport_outside_core hp hclosed,
    cuspPlus_tsupport_norm_bounds hp hclosed, cuspPlus_tsupport_action_gain_eighth hp hE hclosed,
    χ.cuspPlus_weighted_action_gain hp hE hκ hclosed⟩

theorem cuspMinus_support_weighted_action_bounds (hp : p.BasicConditions)
    {E κ : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1) (hκ : κ ∈ Icc (0 : ℝ) (1 / 16))
    {x : Plane} (hx : x ∈ Function.support p.cuspMinus) :
    p.normalCoordinate (reflection x) ∈ Ioo 0 p.t₀ ∧ p.r₀ < ‖x‖ ∧
      ‖x‖ ∈ Icc p.R p.cuspSupportRadius ∧
      bridgeAction p.b E p.R + p.normalCoordinate (reflection x) / 8 ≤
        bridgeAction p.b E ‖x‖ ∧
      κ * χ.weight x - (bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R) ≤
        -p.normalCoordinate (reflection x) / 16 := by
  have hclosed := subset_tsupport p.cuspMinus hx
  exact ⟨cuspMinus_support_normal_bounds p hx, cuspMinus_tsupport_outside_core hp hclosed,
    cuspMinus_tsupport_norm_bounds hp hclosed, cuspMinus_tsupport_action_gain_eighth hp hE hclosed,
    χ.cuspMinus_weighted_action_gain hp hE hκ hclosed⟩

end CuspWeightCutoffs
end InfiniteZero.CuspParameters
