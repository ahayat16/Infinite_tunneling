import InfiniteZero.CuspKernelJetBounds
import InfiniteZero.ConstructionSmooth
import InfiniteZero.ConstructionCuspBounds

/-!
# Log-flat bounds for every jet of the actual cusp potentials

The model kernel estimate is transported through the fixed affine cusp
coordinates and multiplied by the genuine normal cutoff. Outside the closed
cusp support every jet vanishes. Thus any strict loss in the Gaussian
logarithmic exponent controls every fixed Fréchet jet globally in the plane.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 800000

private def cuspFrameMap : Plane →L[ℝ] ℝ × ℝ :=
  (innerSL ℝ cuspNormal).prod (innerSL ℝ cuspTangent)

private theorem tangentCoordinate_eq_inner (p : CuspParameters) (x : Plane) :
    p.tangentCoordinate x = inner ℝ (x - p.cuspTip) cuspTangent := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    cuspTangent, tangentCoordinate, cuspTip, Matrix.vecHead, Matrix.vecTail]
  ring

private theorem cuspFrameMap_coordinates (p : CuspParameters) (x : Plane) :
    cuspFrameMap (x - p.cuspTip) = (p.normalCoordinate x, p.tangentCoordinate x) := by
  ext
  · simp only [cuspFrameMap, ContinuousLinearMap.prod_apply, innerSL_apply_apply,
      normalCoordinate_eq_inner, real_inner_comm]
  · simp only [cuspFrameMap, ContinuousLinearMap.prod_apply, innerSL_apply_apply,
      tangentCoordinate_eq_inner, real_inner_comm]

private theorem norm_jet_affine_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : Plane →L[ℝ] G) {f : G → ℝ} (hf : ContDiff ℝ ∞ f)
    (a x : Plane) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (A (y - a))) x‖ ≤
      ‖iteratedFDeriv ℝ n f (A (x - a))‖ * ‖A‖ ^ n := by
  change ‖iteratedFDeriv ℝ n (fun y => (f ∘ A) (y - a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub,
    A.iteratedFDeriv_comp_right hf (x - a) (by exact_mod_cast le_top)]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n f (A (x - a))) (fun _ : Fin n => A)

private def normalCutoffFactor (p : CuspParameters) (x : Plane) : ℝ :=
  -p.a * p.χa (p.normalCoordinate x)

private def pulledCuspKernel (p : CuspParameters) (x : Plane) : ℝ :=
  cuspKernel p.β p.tStar 0 1 p.χb (p.normalCoordinate x, p.tangentCoordinate x)

private theorem normalCutoffFactor_contDiff {p : CuspParameters} (hp : p.BasicConditions) :
    ContDiff ℝ ∞ (normalCutoffFactor p) :=
  contDiff_const.mul (hp.χa_smooth.comp (normalCoordinate_contDiff p))

private theorem pulledCuspKernel_contDiff {p : CuspParameters} (hp : p.BasicConditions) :
    ContDiff ℝ ∞ (pulledCuspKernel p) :=
  (contDiff_cuspKernel hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) 0 1
    hp.χb_smooth hp.χb_support).comp
    ((normalCoordinate_contDiff p).prodMk (tangentCoordinate_contDiff p))

private theorem exists_normalCutoffFactor_jet_bound {p : CuspParameters}
    (hp : p.BasicConditions) (n : ℕ) :
    ∃ C > 0, ∀ x : Plane, ‖iteratedFDeriv ℝ n (normalCutoffFactor p) x‖ ≤ C := by
  let f : ℝ → ℝ := fun t => -p.a * p.χa t
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul hp.χa_smooth
  have hfc : HasCompactSupport f := hp.χa_support.mul_left
  obtain ⟨C, hC, hbound⟩ := compactSmooth_iteratedDeriv_bounded hf hfc n
  let A : Plane →L[ℝ] ℝ := innerSL ℝ cuspNormal
  have heq : normalCutoffFactor p = fun x => f (A (x - p.cuspTip)) := by
    funext x
    simp only [normalCutoffFactor, f, A, innerSL_apply_apply, normalCoordinate_eq_inner,
      real_inner_comm]
  refine ⟨C * (‖A‖ ^ n + 1), by positivity, ?_⟩
  intro x
  rw [heq]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (A (x - p.cuspTip))‖ * ‖A‖ ^ n :=
      norm_jet_affine_le A hf p.cuspTip x n
    _ ≤ C * ‖A‖ ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        hbound (A (x - p.cuspTip))
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC.le

private theorem exists_pulledCuspKernel_jet_margin_bound {p : CuspParameters}
    (hp : p.BasicConditions) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hgap : β₁ < p.β) (n : ℕ) :
    ∃ C > 0, ∀ x ∈ tsupport p.cuspPlus,
      ‖iteratedFDeriv ℝ n (pulledCuspKernel p) x‖ ≤
        C * logFlat β₁ p.tStar (p.normalCoordinate x) := by
  obtain ⟨C, hC, hbound⟩ := exists_cuspKernel_jet_margin_bound hβ₁ hgap
    (hp.t₀_pos.trans hp.t₀_lt) hp.t₀_pos n 0 (1 : Polynomial ℝ) hp.χb_smooth hp.χb_support
  have hf := contDiff_cuspKernel hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) 0
    (1 : Polynomial ℝ) hp.χb_smooth hp.χb_support
  have heq : pulledCuspKernel p = fun x =>
      cuspKernel p.β p.tStar 0 1 p.χb (cuspFrameMap (x - p.cuspTip)) := by
    funext x
    rw [cuspFrameMap_coordinates]
    rfl
  refine ⟨C * (‖cuspFrameMap‖ ^ n + 1), by positivity, ?_⟩
  intro x hx
  have ht : p.normalCoordinate x ∈ Icc 0 p.t₀ :=
    ⟨(cuspPlus_tsupport_subset_quadratic p hx).1, cuspPlus_tsupport_normal_le p hx⟩
  have hjet := norm_jet_affine_le cuspFrameMap hf p.cuspTip x n
  rw [cuspFrameMap_coordinates] at hjet
  rw [heq]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (cuspKernel p.β p.tStar 0 1 p.χb)
        (p.normalCoordinate x, p.tangentCoordinate x)‖ * ‖cuspFrameMap‖ ^ n := hjet
    _ ≤ (C * logFlat β₁ p.tStar (p.normalCoordinate x)) * ‖cuspFrameMap‖ ^ n :=
      mul_le_mul_of_nonneg_right (hbound _ ht _) (by positivity)
    _ = (C * ‖cuspFrameMap‖ ^ n) * logFlat β₁ p.tStar (p.normalCoordinate x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hC.le) (logFlat_nonneg _ _ _)

/-- Every fixed jet of the genuine upper cusp is controlled globally by any
strictly weaker log-flat profile. The constant is chosen before the point. -/
theorem exists_cuspPlus_jet_margin_bound {p : CuspParameters} (hp : p.BasicConditions)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) (hgap : β₁ < p.β) (n : ℕ) :
    ∃ C > 0, ∀ x : Plane, ‖iteratedFDeriv ℝ n p.cuspPlus x‖ ≤
      C * logFlat β₁ p.tStar (p.normalCoordinate x) := by
  choose A hA hAbound using fun j => exists_normalCutoffFactor_jet_bound hp j
  choose B hB hBbound using fun j => exists_pulledCuspKernel_jet_margin_bound hp hβ₁ hgap j
  let S : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hB (n - i)).le
  refine ⟨S + 1, by positivity, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport p.cuspPlus
  · have heq : p.cuspPlus = fun y => normalCutoffFactor p y * pulledCuspKernel p y := by
      funext y
      simpa only [normalCutoffFactor, pulledCuspKernel, cuspKernel, weightedLogFlat,
        pow_zero, inv_one, Polynomial.eval_one, mul_one, one_mul] using
        cuspPlus_eq_logFlat_formula hp y
    rw [heq]
    apply (norm_iteratedFDeriv_mul_le (normalCutoffFactor_contDiff hp)
      (pulledCuspKernel_contDiff hp) x (by exact_mod_cast le_top)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * A i * (B (n - i) * logFlat β₁ p.tStar (p.normalCoordinate x)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hAbound i x) (Nat.cast_nonneg _))
          (hBbound (n - i) x hx) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hA i).le)
      _ = S * logFlat β₁ p.tStar (p.normalCoordinate x) := by
        simp only [S, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (logFlat_nonneg _ _ _)
  · have hz : iteratedFDeriv ℝ n p.cuspPlus x = 0 := by
      by_contra hn
      exact hx (support_iteratedFDeriv_subset n hn)
    rw [hz, norm_zero]
    exact mul_nonneg (by positivity) (logFlat_nonneg _ _ _)

private def reflectionMap : Plane →L[ℝ] Plane where
  toFun := reflection
  map_add' x y := by
    ext i
    fin_cases i <;> simp [reflection, add_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [reflection]
  cont := reflection_contDiff.continuous

/-- The reflected cusp has the same log-flat jet margin in its reflected
normal coordinate. -/
theorem exists_cuspMinus_jet_margin_bound {p : CuspParameters} (hp : p.BasicConditions)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) (hgap : β₁ < p.β) (n : ℕ) :
    ∃ C > 0, ∀ x : Plane, ‖iteratedFDeriv ℝ n p.cuspMinus x‖ ≤
      C * logFlat β₁ p.tStar (p.normalCoordinate (reflection x)) := by
  obtain ⟨C, hC, hbound⟩ := exists_cuspPlus_jet_margin_bound hp hβ₁ hgap n
  refine ⟨C * (‖reflectionMap‖ ^ n + 1), by positivity, ?_⟩
  intro x
  have heq : p.cuspMinus = p.cuspPlus ∘ reflectionMap := rfl
  rw [heq, reflectionMap.iteratedFDeriv_comp_right (cuspPlus_contDiff hp) x
    (by exact_mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n p.cuspPlus (reflection x)‖ * ‖reflectionMap‖ ^ n := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ n p.cuspPlus (reflectionMap x)) (fun _ : Fin n => reflectionMap)
    _ ≤ (C * logFlat β₁ p.tStar (p.normalCoordinate (reflection x))) * ‖reflectionMap‖ ^ n :=
      mul_le_mul_of_nonneg_right (hbound (reflection x)) (by positivity)
    _ = (C * ‖reflectionMap‖ ^ n) * logFlat β₁ p.tStar (p.normalCoordinate (reflection x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hC.le) (logFlat_nonneg _ _ _)

end InfiniteZero.CuspParameters
