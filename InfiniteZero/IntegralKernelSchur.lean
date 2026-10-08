import InfiniteZero.IntegralKernelCauchySchwarz
import InfiniteZero.MagneticTestGraph

/-!
# The L² bound for an integral kernel with bounded absolute row and column masses

The row estimate is weighted Cauchy–Schwarz. Fubini and the column estimate
then give the global squared-norm bound. These lemmas apply directly to
the explicit magnetic resolvent kernel.
-/
noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem integrable_kernel_mul_bounded {K f : Wavefunction}
    (hK : Integrable K) (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => K x * f x) := by
  apply (hK.norm.mul_const C).mono' (hK.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖K x * f x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

theorem integrable_norm_kernel_mul_sq_bounded {K f : Wavefunction}
    (hK : Integrable K) (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => ‖K x‖ * ‖f x‖ ^ 2) := by
  apply (hK.norm.mul_const (C ^ 2)).mono'
    (hK.aestronglyMeasurable.norm.mul (hf.norm.pow 2).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖‖K x‖ * ‖f x‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hC x) 2) (norm_nonneg _)

/-- Schur's estimate on smooth compact sources. Both absolute kernel
masses are bounded by the same positive number `M`. -/
theorem integralKernel_memLp_mass_bound {K : Plane → Plane → ℂ} {M : ℝ}
    (hM : 0 < M) (hK : Measurable (fun q : Plane × Plane => K q.1 q.2))
    (hrow : ∀ x, Integrable (K x))
    (hcol : ∀ y, Integrable (fun x => K x y))
    (hrowBound : ∀ x, (∫ y : Plane, ‖K x y‖) ≤ M)
    (hcolBound : ∀ y, (∫ x : Plane, ‖K x y‖) ≤ M)
    {f : Wavefunction} (hf : IsTestFunction f) :
    MemLp (fun x => ∫ y : Plane, K x y * f y) 2 volume ∧
      mass (fun x => ∫ y : Plane, K x y * f y) ≤ M ^ 2 * mass f := by
  classical
  let T : Wavefunction := fun x => ∫ y : Plane, K x y * f y
  let H : Plane × Plane → ℝ := fun q => ‖K q.1 q.2‖ * ‖f q.2‖ ^ 2
  have hH : Measurable H := hK.norm.mul ((hf.1.continuous.measurable.comp measurable_snd).norm.pow_const 2)
  have hHnonneg (q : Plane × Plane) : 0 ≤ H q := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hcolNorm (y : Plane) : (∫ x : Plane, ‖H (x, y)‖) =
      (∫ x : Plane, ‖K x y‖) * ‖f y‖ ^ 2 := by
    have heq : (fun x : Plane => ‖H (x, y)‖) =
        (fun x : Plane => ‖K x y‖ * ‖f y‖ ^ 2) := by
      funext x
      exact Real.norm_of_nonneg (hHnonneg (x, y))
    rw [heq, integral_mul_const]
  have hHint : Integrable H (volume.prod volume) := by
    apply (integrable_prod_iff' hH.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun y => (hcol y).norm.mul_const (‖f y‖ ^ 2)
    · apply (hf.integrable_norm_sq.const_mul M).mono'
        hH.norm.stronglyMeasurable.prod_swap.integral_prod_right'.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun y => by
        change ‖∫ x : Plane, ‖H (x, y)‖‖ ≤ M * ‖f y‖ ^ 2
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hcolNorm]
        exact mul_le_mul_of_nonneg_right (hcolBound y) (sq_nonneg _)
  have htotal : (∫ q : Plane × Plane, H q ∂volume.prod volume) ≤ M * mass f := by
    rw [integral_prod_symm _ hHint]
    calc
      _ ≤ ∫ y : Plane, M * ‖f y‖ ^ 2 := by
        apply integral_mono hHint.integral_prod_right (hf.integrable_norm_sq.const_mul M)
        intro y
        change (∫ x : Plane, ‖K x y‖ * ‖f y‖ ^ 2) ≤ M * ‖f y‖ ^ 2
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right (hcolBound y) (sq_nonneg _)
      _ = _ := integral_const_mul _ _
  obtain ⟨C, hC⟩ := hf.2.exists_bound_of_continuous hf.1.continuous
  have hpoint (x : Plane) : ‖T x‖ ^ 2 ≤ M * ∫ y : Plane, H (x, y) := by
    have h1 : Integrable (fun y => ‖K x y‖ * ‖f y‖) := by
      simpa only [norm_mul] using (integrable_kernel_mul_bounded (hrow x) hf.1.continuous hC).norm
    exact integralKernel_row_bound (hrow x) h1
      (integrable_norm_kernel_mul_sq_bounded (hrow x) hf.1.continuous hC) hM (hrowBound x)
  have hT : StronglyMeasurable T :=
    (hK.mul (hf.1.continuous.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'
  have hTsq : Integrable (fun x => ‖T x‖ ^ 2) := by
    apply (hHint.integral_prod_left.const_mul M).mono' (hT.norm.pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
  refine ⟨(memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).mpr hTsq, ?_⟩
  change (∫ x : Plane, ‖T x‖ ^ 2) ≤ _
  calc
    _ ≤ ∫ x : Plane, M * ∫ y : Plane, H (x, y) :=
      integral_mono hTsq (hHint.integral_prod_left.const_mul M) hpoint
    _ = M * ∫ q : Plane × Plane, H q ∂volume.prod volume := by
      rw [integral_const_mul, integral_prod _ hHint]
    _ ≤ M * (M * mass f) := mul_le_mul_of_nonneg_left htotal hM.le
    _ = _ := by ring

end InfiniteZero
