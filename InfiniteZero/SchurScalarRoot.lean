import InfiniteZero.OperatorResolvent
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence of the scalar Schur root

The resolvents here invert a specified self-adjoint operator through their
actual graph certificates. Their uniform norm bound implies continuity in
energy. Positivity at the reference energy and an elementary lower-endpoint
bound then produce a real root, without assuming any ground eigenvector.
-/

noncomputable section
open Set
open scoped NNReal

namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def realSchurFunction (a : ℝ) (B : H) (R : ℝ → H →L[ℂ] H) (E : ℝ) : ℝ :=
  a - E - (inner ℂ B (R E B)).re

theorem re_inner_apply_le_opNorm (R : H →L[ℂ] H) (B : H) :
    (inner ℂ B (R B)).re ≤ ‖R‖ * ‖B‖ ^ 2 := by
  calc
    _ ≤ ‖inner ℂ B (R B)‖ := Complex.re_le_norm _
    _ ≤ ‖B‖ * ‖R B‖ := norm_inner_le_norm _ _
    _ ≤ ‖B‖ * (‖R‖ * ‖B‖) :=
      mul_le_mul_of_nonneg_left (R.le_opNorm B) (norm_nonneg _)
    _ = _ := by ring

theorem realSchurFunction_continuousOn [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (a : ℝ) (B : H)
    {s : Set ℝ} (R : ℝ → H →L[ℂ] H) {C : ℝ≥0}
    (hR : ∀ E ∈ s, IsOperatorResolvent A E (R E))
    (hbound : ∀ E ∈ s, ‖R E‖ ≤ C) :
    ContinuousOn (realSchurFunction a B R) s := by
  have hc := operatorResolvent_continuousOn hA R hR hbound
  have hv : ContinuousOn (fun E => R E B) s := hc.clm_apply continuousOn_const
  exact (continuousOn_const.sub continuousOn_id).sub
    (Complex.continuous_re.comp_continuousOn (continuousOn_const.inner hv))

/-- The left endpoint is explicit and lies below `E₀`. The positive inverse
is only needed at `E₀`; continuity is deduced from the graph identities. -/
theorem exists_realSchurFunction_zero [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {a E₀ : ℝ} (ha : a ≤ E₀)
    (B : H) (R : ℝ → H →L[ℂ] H) {C : ℝ≥0}
    (hR : ∀ E ≤ E₀, IsOperatorResolvent A E (R E))
    (hbound : ∀ E ≤ E₀, ‖R E‖ ≤ C)
    (hpos : 0 ≤ (inner ℂ B (R E₀ B)).re) :
    ∃ E ∈ Icc (a - (C : ℝ) * ‖B‖ ^ 2 - 1) E₀,
      realSchurFunction a B R E = 0 := by
  let lo : ℝ := a - (C : ℝ) * ‖B‖ ^ 2 - 1
  have hlo : lo ≤ E₀ := by
    dsimp [lo]
    nlinarith [mul_nonneg C.coe_nonneg (sq_nonneg ‖B‖)]
  have hc : ContinuousOn (realSchurFunction a B R) (Icc lo E₀) :=
    realSchurFunction_continuousOn hA a B R
      (fun E hE => hR E hE.2) (fun E hE => hbound E hE.2)
  have hupper : realSchurFunction a B R E₀ ≤ 0 := by
    dsimp [realSchurFunction]
    linarith
  have hnorm := (re_inner_apply_le_opNorm (R lo) B).trans
    (mul_le_mul_of_nonneg_right (hbound lo hlo) (sq_nonneg ‖B‖))
  have hlower : 0 ≤ realSchurFunction a B R lo := by
    dsimp [realSchurFunction, lo] at *
    linarith
  exact intermediate_value_Icc' hlo hc ⟨hupper, hlower⟩

end InfiniteZero
