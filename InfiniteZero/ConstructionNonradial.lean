import InfiniteZero.Construction

/-!
# Nonradiality of the fixed cusp potential

A point on the upper outgoing normal has a strictly negative upper cusp
value.  The point on the positive horizontal axis with the same radius lies
outside the core and both cusps.  Thus the constructed potential is nonradial
under the explicit elementary parameter conditions alone.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

def upperNormalPoint (p : CuspParameters) (t : ℝ) : Plane :=
  WithLp.toLp 2 ![p.R / 2 - t / 2, Real.sqrt 3 * p.R / 2 + Real.sqrt 3 * t / 2]

def positiveAxisPoint (r : ℝ) : Plane := WithLp.toLp 2 ![r, 0]

theorem normalCoordinate_upperNormalPoint (p : CuspParameters) (t : ℝ) :
    p.normalCoordinate (p.upperNormalPoint t) = t := by
  simp [normalCoordinate, upperNormalPoint]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem tangentCoordinate_upperNormalPoint (p : CuspParameters) (t : ℝ) :
    p.tangentCoordinate (p.upperNormalPoint t) = 0 := by
  simp [tangentCoordinate, upperNormalPoint]
  ring

theorem norm_positiveAxisPoint {r : ℝ} (hr : 0 ≤ r) :
    ‖positiveAxisPoint r‖ = r := by
  simp [positiveAxisPoint, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq hr]

theorem reflection_positiveAxisPoint (r : ℝ) :
    reflection (positiveAxisPoint r) = positiveAxisPoint r := by
  ext i
  fin_cases i <;> simp [reflection, positiveAxisPoint]

theorem normalCoordinate_positiveAxisPoint (p : CuspParameters) (r : ℝ) :
    p.normalCoordinate (positiveAxisPoint r) = -(r + p.R) / 2 := by
  simp [normalCoordinate, positiveAxisPoint]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem cuspPlus_positiveAxisPoint_eq_zero {p : CuspParameters} (h : p.BasicConditions)
    {r : ℝ} (hr : 0 ≤ r) : p.cuspPlus (positiveAxisPoint r) = 0 := by
  have hn : ¬0 < p.normalCoordinate (positiveAxisPoint r) := by
    rw [normalCoordinate_positiveAxisPoint]
    linarith [h.radius_pos]
  simp [cuspPlus, hn]

theorem potential_positiveAxisPoint_eq_zero {p : CuspParameters} (h : p.BasicConditions)
    {r : ℝ} (hr : p.r₀ ≤ r) : p.potential (positiveAxisPoint r) = 0 := by
  have hr0 : 0 ≤ r := le_trans h.r₀_pos.le hr
  have hplus := cuspPlus_positiveAxisPoint_eq_zero h hr0
  have hcore : p.core (positiveAxisPoint r) = 0 := by
    simp [core, norm_positiveAxisPoint hr0, not_lt.mpr hr]
  simp [potential, hcore, hplus, cuspMinus, reflection_positiveAxisPoint]

/-- The nonradiality requirement of the main theorem is fully verified for
every parameter tuple satisfying the elementary construction conditions. -/
theorem potential_nonradial {p : CuspParameters} (h : p.BasicConditions) :
    ∃ x y : Plane, ‖x‖ = ‖y‖ ∧ p.potential x ≠ p.potential y := by
  obtain ⟨t₂, ht₂, ht₂₀, hχa⟩ := h.χa_one
  let t : ℝ := t₂ / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have ht₀ : t < p.t₀ := by dsimp [t]; linarith
  have hχat : p.χa t = 1 := hχa t ⟨ht.le, by dsimp [t]; linarith⟩
  have hχb0 : p.χb 0 = 1 := h.χb_one 0 ⟨by linarith [h.s₀_pos], by linarith [h.s₀_pos]⟩
  let x : Plane := p.upperNormalPoint t
  have hnx : p.normalCoordinate x = t := normalCoordinate_upperNormalPoint p t
  have htx : p.tangentCoordinate x = 0 := tangentCoordinate_upperNormalPoint p t
  have hplus : p.cuspPlus x < 0 := by
    have hform : p.cuspPlus x = -p.a * Real.exp (-p.β * (Real.log (p.tStar / t)) ^ 2) := by
      simp [cuspPlus, hnx, htx, ht, ht₀, h.s₀_pos, hχat, hχb0]
    rw [hform]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos h.a_pos) (Real.exp_pos _)
  have hvx : p.potential x < 0 := by
    have hcore := (core_range p x).2
    have hminus := (cuspMinus_range h x).2
    have hsum : p.cuspPlus x + p.cuspMinus x < 0 := by linarith
    have hpert := mul_neg_of_pos_of_neg h.ε_pos hsum
    unfold potential
    linarith
  have hrx : p.r₀ ≤ ‖x‖ := by
    have hn := normalCoordinate_le_norm p x
    rw [hnx] at hn
    linarith [h.radius_large, h.r₀_pos]
  refine ⟨x, positiveAxisPoint ‖x‖, ?_, ?_⟩
  · exact (norm_positiveAxisPoint (norm_nonneg x)).symm
  · rw [potential_positiveAxisPoint_eq_zero h hrx]
    exact ne_of_lt hvx

end InfiniteZero.CuspParameters
