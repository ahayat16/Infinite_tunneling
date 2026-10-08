import InfiniteZero.MagneticCovariance

/-!
# Pointwise magnetic IMS identity

The localization identity is proved for the concrete covariant derivatives.
Only differentiability at the evaluation point is needed. No statement about
integration, closed quadratic forms, or preservation of an operator domain is
assumed here.
-/

noncomputable section

open scoped ContDiff

namespace InfiniteZero

/-- A coordinate derivative of a real cutoff. -/
def realPartialDerivative (i : Fin 2) (χ : Plane → ℝ) (x : Plane) : ℝ :=
  fderiv ℝ χ x (coordinateVector i)

/-- Product rule for a real cutoff and a complex wavefunction. -/
theorem partialDerivative_real_mul (i : Fin 2) {χ : Plane → ℝ}
    {ψ : Wavefunction} {x : Plane} (hχ : DifferentiableAt ℝ χ x)
    (hψ : DifferentiableAt ℝ ψ x) :
    partialDerivative i (fun y => (χ y : ℂ) * ψ y) x =
      (χ x : ℂ) * partialDerivative i ψ x +
        (realPartialDerivative i χ x : ℂ) * ψ x := by
  have hd := ((Complex.ofRealCLM.hasFDerivAt).comp x hχ.hasFDerivAt).mul
    hψ.hasFDerivAt
  have he := congrArg (fun f : Plane →L[ℝ] ℂ => f (coordinateVector i)) hd.fderiv
  simpa only [partialDerivative, realPartialDerivative, Function.comp_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, mul_comm] using he

/-- Localization of a concrete covariant momentum. -/
theorem covariantDerivative_real_mul (b coupling : ℝ) (i : Fin 2)
    {χ : Plane → ℝ} {ψ : Wavefunction} {x : Plane}
    (hχ : DifferentiableAt ℝ χ x) (hψ : DifferentiableAt ℝ ψ x) :
    covariantDerivative b coupling i (fun y => (χ y : ℂ) * ψ y) x =
      (χ x : ℂ) * covariantDerivative b coupling i ψ x -
        Complex.I * (realPartialDerivative i χ x : ℂ) * ψ x := by
  rw [covariantDerivative, partialDerivative_real_mul i hχ hψ]
  simp only [covariantDerivative]
  ring

/-- Differentiating a partition of unity cancels its mixed terms. -/
theorem realPartialDerivative_partition (i : Fin 2) {χ₀ χ₁ : Plane → ℝ}
    {x : Plane} (hχ₀ : DifferentiableAt ℝ χ₀ x)
    (hχ₁ : DifferentiableAt ℝ χ₁ x)
    (hpartition : ∀ y, χ₀ y ^ 2 + χ₁ y ^ 2 = 1) :
    χ₀ x * realPartialDerivative i χ₀ x +
      χ₁ x * realPartialDerivative i χ₁ x = 0 := by
  have hd := (hχ₀.hasFDerivAt.mul hχ₀.hasFDerivAt).add
    (hχ₁.hasFDerivAt.mul hχ₁.hasFDerivAt)
  have hf : χ₀ * χ₀ + χ₁ * χ₁ = fun _ => (1 : ℝ) := by
    funext y
    simpa only [pow_two] using hpartition y
  rw [hf] at hd
  have he := congrArg (fun f : Plane →L[ℝ] ℝ => f (coordinateVector i))
    (hd.unique (hasFDerivAt_const (1 : ℝ) x))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul] at he
  change χ₀ x * fderiv ℝ χ₀ x (coordinateVector i) +
    χ₁ x * fderiv ℝ χ₁ x (coordinateVector i) = 0
  linarith

private theorem complex_partition_norm_sq (c₀ c₁ a₀ a₁ : ℝ) (z v : ℂ)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (ha : c₀ * a₀ + c₁ * a₁ = 0) :
    ‖(c₀ : ℂ) * z - Complex.I * (a₀ : ℂ) * v‖ ^ 2 +
      ‖(c₁ : ℂ) * z - Complex.I * (a₁ : ℂ) * v‖ ^ 2 =
      ‖z‖ ^ 2 + (a₀ ^ 2 + a₁ ^ 2) * ‖v‖ ^ 2 := by
  calc
    _ = (c₀ ^ 2 + c₁ ^ 2) * ‖z‖ ^ 2 +
        (a₀ ^ 2 + a₁ ^ 2) * ‖v‖ ^ 2 +
        2 * (c₀ * a₀ + c₁ * a₁) * (z.re * v.im - z.im * v.re) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    _ = _ := by rw [hc, ha]; ring

/-- Pointwise IMS for a single coordinate of the magnetic momentum. -/
theorem covariantDerivative_ims (b coupling : ℝ) (i : Fin 2)
    {χ₀ χ₁ : Plane → ℝ} {ψ : Wavefunction} {x : Plane}
    (hχ₀ : DifferentiableAt ℝ χ₀ x) (hχ₁ : DifferentiableAt ℝ χ₁ x)
    (hψ : DifferentiableAt ℝ ψ x)
    (hpartition : ∀ y, χ₀ y ^ 2 + χ₁ y ^ 2 = 1) :
    ‖covariantDerivative b coupling i (fun y => (χ₀ y : ℂ) * ψ y) x‖ ^ 2 +
      ‖covariantDerivative b coupling i (fun y => (χ₁ y : ℂ) * ψ y) x‖ ^ 2 =
      ‖covariantDerivative b coupling i ψ x‖ ^ 2 +
        ((realPartialDerivative i χ₀ x) ^ 2 +
          (realPartialDerivative i χ₁ x) ^ 2) * ‖ψ x‖ ^ 2 := by
  rw [covariantDerivative_real_mul b coupling i hχ₀ hψ,
    covariantDerivative_real_mul b coupling i hχ₁ hψ]
  exact complex_partition_norm_sq _ _ _ _ _ _ (hpartition x)
    (realPartialDerivative_partition i hχ₀ hχ₁ hpartition)

/-- The pointwise localization error, independent of the magnetic field. -/
def magneticIMSError (χ₀ χ₁ : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, ((realPartialDerivative i χ₀ x) ^ 2 +
    (realPartialDerivative i χ₁ x) ^ 2)

theorem magneticIMSError_nonneg (χ₀ χ₁ : Plane → ℝ) (x : Plane) :
    0 ≤ magneticIMSError χ₀ χ₁ x := by
  exact Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Pointwise IMS summed over both spatial coordinates. -/
theorem magneticKinetic_ims (b coupling : ℝ) {χ₀ χ₁ : Plane → ℝ}
    {ψ : Wavefunction} {x : Plane} (hχ₀ : DifferentiableAt ℝ χ₀ x)
    (hχ₁ : DifferentiableAt ℝ χ₁ x) (hψ : DifferentiableAt ℝ ψ x)
    (hpartition : ∀ y, χ₀ y ^ 2 + χ₁ y ^ 2 = 1) :
    (∑ i : Fin 2, ‖covariantDerivative b coupling i
        (fun y => (χ₀ y : ℂ) * ψ y) x‖ ^ 2) +
      (∑ i : Fin 2, ‖covariantDerivative b coupling i
        (fun y => (χ₁ y : ℂ) * ψ y) x‖ ^ 2) =
      (∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2) +
        magneticIMSError χ₀ χ₁ x * ‖ψ x‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  simp_rw [covariantDerivative_ims b coupling _ hχ₀ hχ₁ hψ hpartition]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rfl

/-- A real square partition preserves the pointwise probability density. -/
theorem realCutoff_mass_partition (c₀ c₁ : ℝ) (z : ℂ)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) :
    ‖(c₀ : ℂ) * z‖ ^ 2 + ‖(c₁ : ℂ) * z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← add_mul, hc, one_mul]

/-- The density integrated in `magneticForm`. -/
def magneticEnergyDensity (b coupling : ℝ) (V : Potential) (ψ : Wavefunction)
    (x : Plane) : ℝ :=
  (∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2) +
    coupling ^ 2 * V x * ‖ψ x‖ ^ 2

/-- The scalar potential localizes without error; only the kinetic term contributes. -/
theorem magneticEnergyDensity_ims (b coupling : ℝ) (V : Potential)
    {χ₀ χ₁ : Plane → ℝ} {ψ : Wavefunction} {x : Plane}
    (hχ₀ : DifferentiableAt ℝ χ₀ x) (hχ₁ : DifferentiableAt ℝ χ₁ x)
    (hψ : DifferentiableAt ℝ ψ x)
    (hpartition : ∀ y, χ₀ y ^ 2 + χ₁ y ^ 2 = 1) :
    magneticEnergyDensity b coupling V (fun y => (χ₀ y : ℂ) * ψ y) x +
      magneticEnergyDensity b coupling V (fun y => (χ₁ y : ℂ) * ψ y) x =
      magneticEnergyDensity b coupling V ψ x +
        magneticIMSError χ₀ χ₁ x * ‖ψ x‖ ^ 2 := by
  have hkin := magneticKinetic_ims b coupling hχ₀ hχ₁ hψ hpartition
  have hmass := realCutoff_mass_partition (χ₀ x) (χ₁ x) (ψ x) (hpartition x)
  simp only [magneticEnergyDensity]
  linear_combination hkin + coupling ^ 2 * V x * hmass

/-- The new density is definitionally the integrand of the existing form. -/
theorem magneticForm_eq_integral_density (b coupling : ℝ) (V : Potential)
    (ψ : Wavefunction) :
    magneticForm b coupling V ψ =
      ∫ x : Plane, magneticEnergyDensity b coupling V ψ x := rfl

end InfiniteZero
