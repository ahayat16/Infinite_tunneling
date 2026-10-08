import InfiniteZero.ConstructionSmooth

/-!
# Every jet vanishes at the cusp tip

All derivatives of a smooth function that vanishes on an open set also vanish
on its closure. We apply this to the negative-normal half-plane, after proving
full smoothness of the zero extension. This proves vanishing of every Fréchet
jet without expanding higher derivatives of the quadratic cusp chart.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero

/-- Boundary jet vanishing for a smooth zero extension. -/
theorem iteratedFDeriv_eq_zero_on_closure
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} {n : ℕ} (hf : ContDiff ℝ n f)
    (hU : IsOpen U) (hzero : EqOn f (fun _ => 0) U) :
    EqOn (iteratedFDeriv ℝ n f) (fun _ => 0) (closure U) := by
  have hjet : EqOn (iteratedFDeriv ℝ n f) (fun _ => 0) U := by
    intro x hx
    have he : f =ᶠ[𝓝 x] (fun _ => 0) :=
      Filter.mem_of_superset (hU.mem_nhds hx) hzero
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (he.iteratedFDeriv ℝ n).self_of_nhds
  exact hjet.closure hf.continuous_iteratedFDeriv' continuous_const

/-- Every jet of every member of the stable cusp family is zero on the entire
line `t = 0`, including points with nonzero tangential coordinate. -/
theorem cuspKernel_iteratedFDeriv_zero_fst {β tStar : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (n k : ℕ) (P : Polynomial ℝ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (u : ℝ) :
    iteratedFDeriv ℝ n (cuspKernel β tStar k P g) (0, u) = 0 := by
  have hzero : EqOn (cuspKernel β tStar k P g) (fun _ => 0)
      (Iio (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    intro z hz
    simp [cuspKernel, weightedLogFlat_of_nonpos β tStar k P (le_of_lt hz.1)]
  have hjet := iteratedFDeriv_eq_zero_on_closure
    (contDiff_cuspKernel_nat hβ hStar n k P hg hgc) (isOpen_Iio.prod isOpen_univ) hzero
  apply hjet
  simp [closure_prod_eq, closure_Iio]

namespace CuspParameters

/-- Along the normal line the affine normal coordinate is exactly its parameter. -/
theorem normalCoordinate_normal_line (p : CuspParameters) (t : ℝ) :
    p.normalCoordinate (p.cuspTip + t • cuspNormal) = t := by
  simp [normalCoordinate, cuspTip, cuspNormal]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem cuspTip_mem_closure_negative_normal (p : CuspParameters) :
    p.cuspTip ∈ closure {x : Plane | p.normalCoordinate x < 0} := by
  let γ : ℝ → Plane := fun t => p.cuspTip + t • cuspNormal
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hm : MapsTo γ (Iio 0) {x : Plane | p.normalCoordinate x < 0} := by
    intro t ht
    simpa only [γ, mem_setOf_eq, normalCoordinate_normal_line] using ht
  have hz : (0 : ℝ) ∈ closure (Iio 0) := by simp [closure_Iio]
  simpa only [γ, zero_smul, add_zero] using hm.closure hγ hz

/-- Full flatness at the upper tip, including the order-zero jet. -/
theorem cuspPlus_iteratedFDeriv_tip {p : CuspParameters} (h : p.BasicConditions) (n : ℕ) :
    iteratedFDeriv ℝ n p.cuspPlus p.cuspTip = 0 := by
  have hzero : EqOn p.cuspPlus (fun _ => 0) {x : Plane | p.normalCoordinate x < 0} := by
    intro x hx
    change p.normalCoordinate x < 0 at hx
    simp [cuspPlus, not_lt.mpr (le_of_lt hx)]
  have hjet := iteratedFDeriv_eq_zero_on_closure
    (contDiff_infty.mp (cuspPlus_contDiff h) n)
    (isOpen_lt (normalCoordinate_contDiff p).continuous continuous_const) hzero
  exact hjet (cuspTip_mem_closure_negative_normal p)

/-- Reflection gives the corresponding vanishing jets at the lower tip. -/
theorem cuspMinus_iteratedFDeriv_tip {p : CuspParameters} (h : p.BasicConditions) (n : ℕ) :
    iteratedFDeriv ℝ n p.cuspMinus (reflection p.cuspTip) = 0 := by
  let U : Set Plane := {x | p.normalCoordinate (reflection x) < 0}
  have hzero : EqOn p.cuspMinus (fun _ => 0) U := by
    intro x hx
    change p.normalCoordinate (reflection x) < 0 at hx
    simp [cuspMinus, cuspPlus, not_lt.mpr (le_of_lt hx)]
  have hm : MapsTo reflection {x : Plane | p.normalCoordinate x < 0} U := by
    intro x hx
    simpa only [U, mem_setOf_eq, reflection_involutive] using hx
  have hclosure : reflection p.cuspTip ∈ closure U :=
    hm.closure reflection_contDiff.continuous (cuspTip_mem_closure_negative_normal p)
  have hjet := iteratedFDeriv_eq_zero_on_closure
    (contDiff_infty.mp (cuspMinus_contDiff h) n)
    (isOpen_lt ((normalCoordinate_contDiff p).continuous.comp reflection_contDiff.continuous)
      continuous_const) hzero
  exact hjet hclosure

end CuspParameters

end InfiniteZero
