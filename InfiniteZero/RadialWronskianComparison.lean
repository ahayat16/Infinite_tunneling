import InfiniteZero.RadialWronskian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Radial comparison from ordered coefficients and an exact exterior tail

For positive solutions with `qf ≤ qg`, the weighted Wronskian is increasing.
If the solutions are proportional on an exterior interval, their Wronskian
vanishes there and is nonpositive everywhere. Hence `f / g` is increasing,
which bounds the entire profile by its exterior multiple of `g`.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

variable {qf qg f df g dg : ℝ → ℝ}

/-- Wronskian derivative for two possibly different radial coefficients. -/
theorem hasDerivAt_radialWronskian_of_coefficients
    (hf : IsRadialODESolutionOn qf f df 0)
    (hg : IsRadialODESolutionOn qg g dg 0) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialWronskian f df g dg)
      (r * (qg r - qf r) * f r * g r) r := by
  have hd := (hasDerivAt_id r).mul
    (((hf.deriv r hr).mul (hg.second r hr)).sub
      ((hf.second r hr).mul (hg.deriv r hr)))
  convert hd using 1
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  field_simp [hr.ne']
  ring

/-- Matching exterior tails force the ordered-coefficient Wronskian to be
nonpositive at every positive radius. -/
theorem radialWronskian_nonpos_of_coefficient_le_tail
    (hf : IsRadialODESolutionOn qf f df 0)
    (hg : IsRadialODESolutionOn qg g dg 0)
    (hfpos : ∀ r ∈ Ioi (0 : ℝ), 0 < f r)
    (hgpos : ∀ r ∈ Ioi (0 : ℝ), 0 < g r)
    (hq : ∀ r ∈ Ioi (0 : ℝ), qf r ≤ qg r)
    {a Γ : ℝ} (ha : 0 < a) (htail : ∀ r ∈ Ioi a, f r = Γ * g r)
    {r : ℝ} (hr : 0 < r) : radialWronskian f df g dg r ≤ 0 := by
  have hmono : MonotoneOn (radialWronskian f df g dg) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro s hs
      exact (hasDerivAt_radialWronskian_of_coefficients hf hg hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs0 : 0 < s := interior_subset hs
      exact (hasDerivAt_radialWronskian_of_coefficients hf hg hs0).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 < s := interior_subset hs
      rw [(hasDerivAt_radialWronskian_of_coefficients hf hg hs0).deriv]
      exact mul_nonneg (mul_nonneg (mul_nonneg hs0.le (sub_nonneg.mpr (hq s hs0)))
        (hfpos s hs0).le) (hgpos s hs0).le
  let R := max a r + 1
  have hRa : a < R := (le_max_left a r).trans_lt (lt_add_one _)
  have hRr : r < R := (le_max_right a r).trans_lt (lt_add_one _)
  have hRpos : 0 < R := ha.trans hRa
  have heq : f =ᶠ[𝓝 R] (fun s => Γ * g s) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hRa) fun s hs => htail s hs
  have hd : df R = Γ * dg R :=
    (hf.deriv R hRpos).unique (((hg.deriv R hRpos).const_mul Γ).congr_of_eventuallyEq heq)
  have hzero : radialWronskian f df g dg R = 0 := by
    rw [radialWronskian, htail R hRa, hd]
    ring
  exact (hmono hr hRpos hRr.le).trans_eq hzero

/-- A positive radial solution with smaller coefficient lies below its
exact exterior multiple of the positive comparison solution. -/
theorem le_mul_of_radialODE_coefficient_le
    (hf : IsRadialODESolutionOn qf f df 0)
    (hg : IsRadialODESolutionOn qg g dg 0)
    (hfpos : ∀ r ∈ Ioi (0 : ℝ), 0 < f r)
    (hgpos : ∀ r ∈ Ioi (0 : ℝ), 0 < g r)
    (hq : ∀ r ∈ Ioi (0 : ℝ), qf r ≤ qg r)
    {a Γ : ℝ} (ha : 0 < a) (htail : ∀ r ∈ Ioi a, f r = Γ * g r)
    {r : ℝ} (hr : 0 < r) : f r ≤ Γ * g r := by
  have hratio (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun t => f t / g t)
        ((df s * g s - f s * dg s) / (g s) ^ 2) s :=
    (hf.deriv s hs).div (hg.deriv s hs) (hgpos s hs).ne'
  have hmono : MonotoneOn (fun s => f s / g s) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro s hs
      exact (hratio s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hratio s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 < s := interior_subset hs
      rw [(hratio s hs0).deriv]
      apply div_nonneg _ (sq_nonneg _)
      have hw := radialWronskian_nonpos_of_coefficient_le_tail
        hf hg hfpos hgpos hq ha htail hs0
      unfold radialWronskian at hw
      nlinarith
  let R := max a r + 1
  have hRa : a < R := (le_max_left a r).trans_lt (lt_add_one _)
  have hRr : r < R := (le_max_right a r).trans_lt (lt_add_one _)
  have hRpos : 0 < R := ha.trans hRa
  have hbound := hmono hr hRpos hRr.le
  dsimp only at hbound
  rw [htail R hRa, mul_div_cancel_right₀ Γ (hgpos R hRpos).ne'] at hbound
  exact (div_le_iff₀ (hgpos r hr)).mp hbound

end InfiniteZero
