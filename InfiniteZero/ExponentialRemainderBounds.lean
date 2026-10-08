import InfiniteZero.ComplexLogFlatPhase
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv

/-!
# Uniform bounds for the exponential remainder

The real remainder `exp (-q) - 1 + q` is quadratic at zero and grows at
least linearly in both tails. These estimates survive the saddle scaling
`q = x / sqrt A` with constants independent of `A ≥ 1`.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

@[simp] theorem exponentialRemainder_zero : exponentialRemainder 0 = 0 := by
  simp [exponentialRemainder]

theorem hasDerivAt_exponentialRemainder (q : ℝ) :
    HasDerivAt exponentialRemainder (1 - Real.exp (-q)) q := by
  convert (((hasDerivAt_id q).neg.exp).sub_const 1).add (hasDerivAt_id q) using 1
  simp
  ring

theorem hasDerivAt_exponentialRemainder_derivative (q : ℝ) :
    HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-q)) q := by
  convert ((hasDerivAt_id q).neg.exp).const_sub 1 using 1
  simp

theorem continuous_exponentialRemainder : Continuous exponentialRemainder :=
  continuous_iff_continuousAt.2 fun q => (hasDerivAt_exponentialRemainder q).continuousAt

private theorem exp_neg_one_le_half : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
  have he := Real.add_one_le_exp (1 : ℝ)
  rw [Real.exp_neg]
  simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ Real.exp 1))

/-- A quadratic lower bound on the whole half-line `q ≤ 1`. -/
theorem exponentialRemainder_quadratic_lower {q : ℝ} (hq : q ≤ 1) :
    Real.exp (-1) / 2 * q ^ 2 ≤ exponentialRemainder q := by
  by_cases hq0 : q ≤ 0
  · have he := Real.quadratic_le_exp_of_nonneg (neg_nonneg.2 hq0)
    have hsmall : Real.exp (-1 : ℝ) ≤ 1 := by
      simp
    dsimp [exponentialRemainder]
    nlinarith [mul_nonneg (sub_nonneg.2 hsmall) (sq_nonneg q)]
  have hq0 : 0 ≤ q := le_of_not_ge hq0
  let g : ℝ → ℝ := fun t => 1 - Real.exp (-t) - Real.exp (-1) * t
  have hg (t : ℝ) : HasDerivAt g (Real.exp (-t) - Real.exp (-1)) t := by
    simpa using (hasDerivAt_exponentialRemainder_derivative t).sub
      ((hasDerivAt_id t).const_mul (Real.exp (-1)))
  have hgm : MonotoneOn g (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((show Differentiable ℝ g from fun t => (hg t).differentiableAt).continuous.continuousOn)
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hg t).deriv, sub_nonneg]
    exact Real.exp_le_exp.mpr (neg_le_neg (interior_subset ht).2)
  have hgpos (t : ℝ) (ht : t ∈ Icc 0 1) : 0 ≤ g t := by
    simpa [g] using hgm (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
  let f : ℝ → ℝ := fun t => exponentialRemainder t - Real.exp (-1) / 2 * t ^ 2
  have hf (t : ℝ) : HasDerivAt f (g t) t := by
    convert (hasDerivAt_exponentialRemainder t).sub
      (((hasDerivAt_id t).pow 2).const_mul (Real.exp (-1) / 2)) using 1
    simp [g]
    ring
  have hfm : MonotoneOn f (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((show Differentiable ℝ f from fun t => (hf t).differentiableAt).continuous.continuousOn)
      (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hf t).deriv]
    exact hgpos t (interior_subset ht)
  have := hfm (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hq0, hq⟩ hq0
  simpa [f, sub_nonneg] using this

/-- The positive tail has a linear lower bound, with a stronger constant. -/
theorem exponentialRemainder_linear_lower {q : ℝ} (hq : 1 ≤ q) :
    Real.exp (-1) * q ≤ exponentialRemainder q := by
  let f : ℝ → ℝ := fun t => exponentialRemainder t - Real.exp (-1) * t
  have hf (t : ℝ) : HasDerivAt f (1 - Real.exp (-t) - Real.exp (-1)) t := by
    simpa using (hasDerivAt_exponentialRemainder t).sub
      ((hasDerivAt_id t).const_mul (Real.exp (-1)))
  have hm : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      ((show Differentiable ℝ f from fun t => (hf t).differentiableAt).continuous.continuousOn)
      (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hf t).deriv]
    have he : Real.exp (-t) ≤ Real.exp (-1 : ℝ) :=
      Real.exp_le_exp.mpr (neg_le_neg (interior_subset ht))
    linarith [exp_neg_one_le_half]
  have := hm (show (1 : ℝ) ∈ Ici 1 by norm_num) hq hq
  simpa [f, exponentialRemainder, sub_nonneg] using this

/-- A single strictly positive constant controls both the Gaussian core and the tails. -/
theorem exponentialRemainder_quadratic_linear_lower (q : ℝ) :
    Real.exp (-1) / 2 * min (q ^ 2) |q| ≤ exponentialRemainder q := by
  by_cases hq : q ≤ 1
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
      (exponentialRemainder_quadratic_lower hq)
  have hq : 1 ≤ q := le_of_not_ge hq
  have habs : |q| = q := abs_of_nonneg (by linarith)
  calc
    Real.exp (-1) / 2 * min (q ^ 2) |q| ≤ Real.exp (-1) / 2 * q := by
      rw [habs]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ ≤ Real.exp (-1) * q := by
      nlinarith [mul_nonneg (Real.exp_pos (-1)).le (show 0 ≤ q by linarith)]
    _ ≤ exponentialRemainder q := exponentialRemainder_linear_lower hq

theorem exponentialRemainder_lower_constant_pos : 0 < Real.exp (-1 : ℝ) / 2 := by
  positivity

/-- The quadratic-linear bound is uniform under the saddle scaling. -/
theorem exponentialRemainder_scaled_lower {A : ℝ} (hA : 1 ≤ A) (x : ℝ) :
    Real.exp (-1) / 2 * min (x ^ 2) |x| ≤
      A * exponentialRemainder (x / Real.sqrt A) := by
  have hApos : 0 < A := by linarith
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hs1 : 1 ≤ Real.sqrt A := Real.one_le_sqrt.2 hA
  have hs2 := Real.sq_sqrt hApos.le
  have hquad : A * (x / Real.sqrt A) ^ 2 = x ^ 2 := by
    rw [div_pow, hs2]
    field_simp
  have hlin : A * |x / Real.sqrt A| = Real.sqrt A * |x| := by
    rw [abs_div, abs_of_pos hs]
    field_simp
    nlinarith only [congrArg (fun r : ℝ => r * |x|) hs2]
  have hmin : min (x ^ 2) |x| ≤ A * min ((x / Real.sqrt A) ^ 2) |x / Real.sqrt A| := by
    rw [mul_min_of_nonneg _ _ hApos.le, hquad, hlin]
    exact min_le_min le_rfl (by nlinarith [abs_nonneg x])
  calc
    Real.exp (-1) / 2 * min (x ^ 2) |x| ≤
        Real.exp (-1) / 2 * (A * min ((x / Real.sqrt A) ^ 2) |x / Real.sqrt A|) :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = A * (Real.exp (-1) / 2 * min ((x / Real.sqrt A) ^ 2) |x / Real.sqrt A|) := by ring
    _ ≤ A * exponentialRemainder (x / Real.sqrt A) :=
      mul_le_mul_of_nonneg_left (exponentialRemainder_quadratic_linear_lower _) hApos.le

/-- The precise quadratic coefficient at the saddle. -/
theorem tendsto_exponentialRemainder_div_sq :
    Tendsto (fun q : ℝ => exponentialRemainder q / q ^ 2)
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hd : HasDerivAt (fun q : ℝ => 1 - Real.exp (-q)) 1 0 := by
    simpa using hasDerivAt_exponentialRemainder_derivative 0
  have hslope := hd.tendsto_slope.div_const 2
  simp only [slope_def_field, neg_zero, Real.exp_zero, sub_self, sub_zero] at hslope
  have hdiv : Tendsto (fun q : ℝ => (1 - Real.exp (-q)) / (2 * q))
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
    convert hslope using 1
    ext q
    ring
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun q => 1 - Real.exp (-q)) (g' := fun q => 2 * q)
    (a := 0) _ _ _ _ _ hdiv
  · exact Eventually.of_forall hasDerivAt_exponentialRemainder
  · exact Eventually.of_forall fun q => by
      convert (hasDerivAt_id q).pow 2 using 1
      simp
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact mul_ne_zero (by norm_num) hq
  · simpa using (continuous_exponentialRemainder.continuousAt.tendsto
      (x := (0 : ℝ))).mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · simpa using ((continuousAt_id (x := (0 : ℝ))).pow 2).tendsto.mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)

/-- Pointwise Gaussian scaling of the remainder as the saddle parameter grows. -/
theorem tendsto_scaled_exponentialRemainder (x : ℝ) :
    Tendsto (fun A : ℝ => A * exponentialRemainder (x / Real.sqrt A))
      atTop (𝓝 (x ^ 2 / 2)) := by
  by_cases hx : x = 0
  · subst x
    simp
  have hroot : Tendsto (fun A : ℝ => (Real.sqrt A)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have harg : Tendsto (fun A : ℝ => x / Real.sqrt A) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa [div_eq_mul_inv] using hroot.const_mul x
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
      exact div_ne_zero hx (Real.sqrt_pos.2 (by linarith)).ne'
  have hlim := (tendsto_exponentialRemainder_div_sq.comp harg).const_mul (x ^ 2)
  have hlim' : Tendsto
      (fun A : ℝ => x ^ 2 * (exponentialRemainder (x / Real.sqrt A) /
        (x / Real.sqrt A) ^ 2)) atTop (𝓝 (x ^ 2 / 2)) := by
    simpa only [Function.comp_apply, mul_one_div] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
  have hApos : 0 < A := by linarith
  rw [div_pow, Real.sq_sqrt hApos.le]
  field_simp

end InfiniteZero
