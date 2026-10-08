import InfiniteZero.ConstructionSupportSeparation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# A fixed Lipschitz weight for the two cusp supports

Smooth compact cutoffs isolate the two closed cusp supports from each other
and from the ball of radius `4 * r₀`. Multiplying their nonnegative normal
coordinates by these cutoffs gives the weight of LA.1. The parameters and
the Lipschitz constant are fixed before any coupling is chosen.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology Manifold NNReal

namespace InfiniteZero.CuspParameters

private theorem exists_compact_smooth_cutoff {K U : Set Plane}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : Plane → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ EqOn χ 1 K ∧ tsupport χ ⊆ U := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Plane)
  have hopen : IsOpen (U ∩ Metric.ball (0 : Plane) R) := hU.inter Metric.isOpen_ball
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset
    (hopen.mem_nhdsSet.mpr (subset_inter hKU hR))
  obtain ⟨χ, hzero, hone, hrange⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (𝓘(ℝ, Plane))
      hV.isClosed_compl hK.isClosed
      (Set.disjoint_left.mpr (fun x hx hxK => hx (hKV hxK))) (n := (⊤ : ℕ∞))
  have hsupp : tsupport (χ : Plane → ℝ) ⊆ closure V := by
    apply closure_mono
    intro x hx
    by_contra hxV
    exact hx (hzero hxV)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, hrange, hone,
    fun x hx => (hVU (hsupp hx)).1⟩
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) R)
  intro x hx
  exact Metric.ball_subset_closedBall ((hVU (hsupp (subset_closure hx))).2)

/-- The smooth cutoffs used in the positive-part cusp weight. Their closed
supports avoid the core ball and the opposite closed cusp support. -/
structure CuspWeightCutoffs (p : CuspParameters) where
  plus : Plane → ℝ
  minus : Plane → ℝ
  plus_smooth : ContDiff ℝ ∞ plus
  minus_smooth : ContDiff ℝ ∞ minus
  plus_compact : HasCompactSupport plus
  minus_compact : HasCompactSupport minus
  plus_range : ∀ x, plus x ∈ Icc 0 1
  minus_range : ∀ x, minus x ∈ Icc 0 1
  plus_one : EqOn plus 1 (tsupport p.cuspPlus)
  minus_one : EqOn minus 1 (tsupport p.cuspMinus)
  plus_tsupport : tsupport plus ⊆
    (Metric.closedBall 0 (4 * p.r₀) ∪ tsupport p.cuspMinus)ᶜ
  minus_tsupport : tsupport minus ⊆
    (Metric.closedBall 0 (4 * p.r₀) ∪ tsupport p.cuspPlus)ᶜ

/-- The actual closed supports admit the required smooth compact cutoffs. -/
theorem exists_cuspWeightCutoffs {p : CuspParameters} (hp : p.BasicConditions) :
    Nonempty (CuspWeightCutoffs p) := by
  have hplus : tsupport p.cuspPlus ⊆
      (Metric.closedBall 0 (4 * p.r₀) ∪ tsupport p.cuspMinus)ᶜ := by
    intro x hx hbad
    rcases hbad with hball | hminus
    · rw [Metric.mem_closedBall, dist_zero_right] at hball
      linarith [cuspPlus_tsupport_norm_lower p hx, hp.radius_large]
    · exact (Set.disjoint_left.mp (cuspPlus_cuspMinus_tsupport_disjoint hp)) hx hminus
  have hminus : tsupport p.cuspMinus ⊆
      (Metric.closedBall 0 (4 * p.r₀) ∪ tsupport p.cuspPlus)ᶜ := by
    intro x hx hbad
    rcases hbad with hball | hplus
    · rw [Metric.mem_closedBall, dist_zero_right] at hball
      linarith [cuspMinus_tsupport_norm_lower p hx, hp.radius_large]
    · exact (Set.disjoint_left.mp (cuspPlus_cuspMinus_tsupport_disjoint hp)) hplus hx
  obtain ⟨χp, hχp, hcp, hrp, hop, hsp⟩ := exists_compact_smooth_cutoff
    (cuspPlus_hasCompactSupport hp)
    ((Metric.isClosed_closedBall.union (isClosed_tsupport p.cuspMinus)).isOpen_compl) hplus
  obtain ⟨χm, hχm, hcm, hrm, hom, hsm⟩ := exists_compact_smooth_cutoff
    (cuspMinus_hasCompactSupport hp)
    ((Metric.isClosed_closedBall.union (isClosed_tsupport p.cuspPlus)).isOpen_compl) hminus
  exact ⟨⟨χp, χm, hχp, hχm, hcp, hcm, hrp, hrm, hop, hom, hsp, hsm⟩⟩

namespace CuspWeightCutoffs

variable {p : CuspParameters} (χ : CuspWeightCutoffs p)

/-- The compactly supported nonnegative Lipschitz weight of LA.1. -/
def weight (x : Plane) : ℝ :=
  χ.plus x * max (p.normalCoordinate x) 0 +
    χ.minus x * max (p.normalCoordinate (reflection x)) 0

theorem weight_nonneg (x : Plane) : 0 ≤ χ.weight x :=
  add_nonneg (mul_nonneg (χ.plus_range x).1 (le_max_right _ _))
    (mul_nonneg (χ.minus_range x).1 (le_max_right _ _))

theorem plus_zero_on_core {x : Plane} (hx : ‖x‖ ≤ 4 * p.r₀) : χ.plus x = 0 := by
  by_contra hn
  exact χ.plus_tsupport (subset_closure hn) (Or.inl (by simpa using hx))

theorem minus_zero_on_core {x : Plane} (hx : ‖x‖ ≤ 4 * p.r₀) : χ.minus x = 0 := by
  by_contra hn
  exact χ.minus_tsupport (subset_closure hn) (Or.inl (by simpa using hx))

theorem weight_zero_on_core {x : Plane} (hx : ‖x‖ ≤ 4 * p.r₀) : χ.weight x = 0 := by
  simp only [weight, χ.plus_zero_on_core hx, χ.minus_zero_on_core hx, zero_mul, zero_add]

theorem plus_zero_on_minus {x : Plane} (hx : x ∈ tsupport p.cuspMinus) : χ.plus x = 0 := by
  by_contra hn
  exact χ.plus_tsupport (subset_closure hn) (Or.inr hx)

theorem minus_zero_on_plus {x : Plane} (hx : x ∈ tsupport p.cuspPlus) : χ.minus x = 0 := by
  by_contra hn
  exact χ.minus_tsupport (subset_closure hn) (Or.inr hx)

theorem weight_eq_normal_on_plus {x : Plane} (hx : x ∈ tsupport p.cuspPlus) :
    χ.weight x = p.normalCoordinate x := by
  have ht := (cuspPlus_tsupport_subset_quadratic p hx).1
  simp only [weight, χ.plus_one hx, Pi.one_apply, χ.minus_zero_on_plus hx,
    zero_mul, add_zero, one_mul, max_eq_left ht]

theorem weight_eq_normal_on_minus {x : Plane} (hx : x ∈ tsupport p.cuspMinus) :
    χ.weight x = p.normalCoordinate (reflection x) := by
  have hxr : reflection x ∈ tsupport p.cuspPlus :=
    tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
  have ht := (cuspPlus_tsupport_subset_quadratic p hxr).1
  simp only [weight, χ.minus_one hx, Pi.one_apply, χ.plus_zero_on_minus hx,
    zero_mul, zero_add, one_mul, max_eq_left ht]

theorem weight_hasCompactSupport : HasCompactSupport χ.weight := by
  exact χ.plus_compact.mul_right.add χ.minus_compact.mul_right

/-- Moving the positive part outside the nonnegative cutoff reduces the
Lipschitz bound to two smooth compactly supported functions. -/
theorem weight_eq_max (x : Plane) :
    χ.weight x = max (χ.plus x * p.normalCoordinate x) 0 +
      max (χ.minus x * p.normalCoordinate (reflection x)) 0 := by
  simp only [weight, mul_max_of_nonneg _ _ (χ.plus_range x).1,
    mul_max_of_nonneg _ _ (χ.minus_range x).1, mul_zero]

theorem weight_lipschitz : ∃ C : ℝ≥0, LipschitzWith C χ.weight := by
  have hcp : HasCompactSupport (fun x => χ.plus x * p.normalCoordinate x) :=
    χ.plus_compact.mul_right
  have hcm : HasCompactSupport (fun x => χ.minus x * p.normalCoordinate (reflection x)) :=
    χ.minus_compact.mul_right
  obtain ⟨Cp, hp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcp
    (χ.plus_smooth.mul (normalCoordinate_contDiff p)) (by simp)
  obtain ⟨Cm, hm⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcm
    (χ.minus_smooth.mul ((normalCoordinate_contDiff p).comp reflection_contDiff)) (by simp)
  refine ⟨Cp + Cm, ?_⟩
  convert (hp.max_const 0).add (hm.max_const 0) using 1
  exact funext χ.weight_eq_max

end CuspWeightCutoffs

/-- A complete existence statement for the fixed cusp weight, independent of
all coupling and well-separation parameters. -/
theorem exists_cuspWeight {p : CuspParameters} (hp : p.BasicConditions) :
    ∃ (T : Plane → ℝ) (C : ℝ≥0),
      (∀ x, 0 ≤ T x) ∧ HasCompactSupport T ∧ LipschitzWith C T ∧
      (∀ x, ‖x‖ ≤ 4 * p.r₀ → T x = 0) ∧
      (∀ x ∈ tsupport p.cuspPlus, T x = p.normalCoordinate x) ∧
      (∀ x ∈ tsupport p.cuspMinus, T x = p.normalCoordinate (reflection x)) := by
  obtain ⟨χ⟩ := exists_cuspWeightCutoffs hp
  obtain ⟨C, hC⟩ := χ.weight_lipschitz
  exact ⟨χ.weight, C, χ.weight_nonneg, χ.weight_hasCompactSupport, hC,
    fun _ hx => χ.weight_zero_on_core hx,
    fun _ hx => χ.weight_eq_normal_on_plus hx,
    fun _ hx => χ.weight_eq_normal_on_minus hx⟩

end InfiniteZero.CuspParameters
