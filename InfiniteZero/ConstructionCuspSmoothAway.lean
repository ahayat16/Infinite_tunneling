import InfiniteZero.ConstructionCompact
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# All regular points of the zero-extended cusp

The cutoff support hypotheses remove the artificial lateral/outer chart
boundaries. On the nonpositive normal half-plane, the closed quadratic cusp
can meet the zero-normal line only at its tip. Thus the only remaining
smoothness obligation is at that single point, not on a whole boundary.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace InfiniteZero.CuspParameters

theorem normalCoordinate_contDiff (p : CuspParameters) :
    ContDiff ℝ ∞ p.normalCoordinate := by
  unfold normalCoordinate
  fun_prop

theorem tangentCoordinate_contDiff (p : CuspParameters) :
    ContDiff ℝ ∞ p.tangentCoordinate := by
  unfold tangentCoordinate
  fun_prop

theorem reflection_contDiff : ContDiff ℝ ∞ reflection := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Plane => x 0)
    exact contDiff_piLp_apply 2
  · change ContDiff ℝ ∞ (fun x : Plane => -x 1)
    exact (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (i := (1 : Fin 2)) 2).neg

theorem cuspPlus_eq_formula_of_normal_pos {p : CuspParameters}
    (h : p.BasicConditions) {x : Plane} (ht : 0 < p.normalCoordinate x) :
    p.cuspPlus x = -p.a * Real.exp (-p.β * (Real.log (p.tStar / p.normalCoordinate x)) ^ 2) *
      p.χa (p.normalCoordinate x) * p.χb (p.tangentCoordinate x / p.normalCoordinate x ^ 2) := by
  by_cases ha : p.normalCoordinate x < p.t₀
  · by_cases hb : |p.tangentCoordinate x / p.normalCoordinate x ^ 2| < p.s₀
    · simp [cuspPlus, ht, ha, hb]
    · have hzero : p.χb (p.tangentCoordinate x / p.normalCoordinate x ^ 2) = 0 := by
        by_contra hn
        have hs := h.χb_localization (subset_tsupport p.χb hn)
        exact hb (abs_lt.mpr hs)
      simp [cuspPlus, ht, ha, hb, hzero]
  · have hzero : p.χa (p.normalCoordinate x) = 0 := by
      by_contra hn
      exact ha (h.χa_localization (subset_tsupport p.χa hn)).2
    simp [cuspPlus, ht, ha, hzero]

theorem cuspPlus_contDiffAt_of_normal_pos {p : CuspParameters}
    (h : p.BasicConditions) {x : Plane} (ht : 0 < p.normalCoordinate x) :
    ContDiffAt ℝ ∞ p.cuspPlus x := by
  have hn := (normalCoordinate_contDiff p).contDiffAt (x := x)
  have hu := (tangentCoordinate_contDiff p).contDiffAt (x := x)
  have htStar : 0 < p.tStar := lt_trans h.t₀_pos h.t₀_lt
  have hlog : ContDiffAt ℝ ∞ (fun y => Real.log (p.tStar / p.normalCoordinate y)) x :=
    (contDiffAt_const.div hn (ne_of_gt ht)).log (div_ne_zero (ne_of_gt htStar) (ne_of_gt ht))
  have hs : ContDiffAt ℝ ∞
      (fun y => p.tangentCoordinate y / p.normalCoordinate y ^ 2) x :=
    hu.div (hn.pow 2) (pow_ne_zero _ (ne_of_gt ht))
  have hf : ContDiffAt ℝ ∞
      (fun y => -p.a * Real.exp (-p.β * (Real.log (p.tStar / p.normalCoordinate y)) ^ 2) *
        p.χa (p.normalCoordinate y) * p.χb (p.tangentCoordinate y / p.normalCoordinate y ^ 2)) x :=
    ((contDiffAt_const.mul ((contDiffAt_const.mul (hlog.pow 2)).exp)).mul
      (h.χa_smooth.contDiffAt.comp x hn)).mul (h.χb_smooth.contDiffAt.comp x hs)
  apply hf.congr_of_eventuallyEq
  have he : ∀ᶠ y in 𝓝 x, 0 < p.normalCoordinate y :=
    (normalCoordinate_contDiff p).continuous.continuousAt.eventually (Ioi_mem_nhds ht)
  filter_upwards [he] with y hy
  exact cuspPlus_eq_formula_of_normal_pos h hy

/-- The topological support lies in the closed quadratic cusp, including the tip. -/
theorem cuspPlus_tsupport_subset_quadratic (p : CuspParameters) :
    tsupport p.cuspPlus ⊆ {x | 0 ≤ p.normalCoordinate x ∧
      |p.tangentCoordinate x| ≤ p.s₀ * p.normalCoordinate x ^ 2} := by
  apply closure_minimal
  · intro x hx
    have hc : 0 < p.normalCoordinate x ∧ p.normalCoordinate x < p.t₀ ∧
        |p.tangentCoordinate x / p.normalCoordinate x ^ 2| < p.s₀ := by
      by_contra hn
      exact hx (by simp [cuspPlus, hn])
    refine ⟨hc.1.le, ?_⟩
    have ht2 : 0 < p.normalCoordinate x ^ 2 := sq_pos_of_pos hc.1
    rw [abs_div, abs_of_pos ht2] at hc
    exact ((div_lt_iff₀ ht2).mp hc.2.2).le
  · exact (isClosed_le continuous_const (normalCoordinate_contDiff p).continuous).inter
      (isClosed_le (tangentCoordinate_contDiff p).continuous.abs
        (continuous_const.mul ((normalCoordinate_contDiff p).continuous.pow 2)))

theorem cuspPlus_notMem_tsupport_of_normal_nonpos {p : CuspParameters} {x : Plane}
    (ht : p.normalCoordinate x ≤ 0) (hx : x ≠ p.cuspTip) : x ∉ tsupport p.cuspPlus := by
  intro hs
  have hc := cuspPlus_tsupport_subset_quadratic p hs
  have hn : p.normalCoordinate x = 0 := le_antisymm ht hc.1
  have hu : p.tangentCoordinate x = 0 := by
    apply abs_eq_zero.mp
    have huabs : |p.tangentCoordinate x| ≤ 0 := by simpa only [hn, zero_pow (by decide : 2 ≠ 0), mul_zero] using hc.2
    exact le_antisymm huabs (abs_nonneg (p.tangentCoordinate x))
  apply hx
  simpa only [hn, hu, zero_smul, add_zero] using cuspFrame_reconstruction p x

theorem cuspPlus_contDiffAt_of_ne_tip {p : CuspParameters}
    (h : p.BasicConditions) {x : Plane} (hx : x ≠ p.cuspTip) :
    ContDiffAt ℝ ∞ p.cuspPlus x := by
  by_cases ht : 0 < p.normalCoordinate x
  · exact cuspPlus_contDiffAt_of_normal_pos h ht
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    exact notMem_tsupport_iff_eventuallyEq.mp
      (cuspPlus_notMem_tsupport_of_normal_nonpos (le_of_not_gt ht) hx)

/-- No smoothness of a chart boundary is left hidden in this reduction. -/
theorem cuspPlus_contDiff_iff_tip {p : CuspParameters} (h : p.BasicConditions) :
    ContDiff ℝ ∞ p.cuspPlus ↔ ContDiffAt ℝ ∞ p.cuspPlus p.cuspTip := by
  refine ⟨fun hs => hs.contDiffAt, fun hs => contDiff_iff_contDiffAt.mpr ?_⟩
  intro x
  by_cases hx : x = p.cuspTip
  · simpa only [hx] using hs
  · exact cuspPlus_contDiffAt_of_ne_tip h hx

end InfiniteZero.CuspParameters
