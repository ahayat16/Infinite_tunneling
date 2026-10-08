import InfiniteZero.MagneticCovariance

/-!
# Derivatives under a planar affine rescaling

The dilation factor acts on every argument of a Fréchet jet. In particular,
coordinate derivatives acquire one factor per derivative, including at zero
or negative dilation factors.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

def affineScale (x₀ : Plane) (h : ℝ) (y : Plane) : Plane := x₀ + h • y

theorem contDiff_affineScale (x₀ : Plane) (h : ℝ) :
    ContDiff ℝ ∞ (affineScale x₀ h) :=
  contDiff_const.add (contDiff_id.const_smul h)

theorem iteratedFDeriv_affineScale {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (x₀ : Plane) (h : ℝ) (n : ℕ) (y : Plane) :
    iteratedFDeriv ℝ n (u ∘ affineScale x₀ h) y =
      h ^ n • iteratedFDeriv ℝ n u (affineScale x₀ h y) := by
  let A : Plane →L[ℝ] Plane := h • ContinuousLinearMap.id ℝ Plane
  have hf : ContDiff ℝ ∞ (fun z => u (x₀ + z)) :=
    hu.comp (contDiff_const.add contDiff_id)
  change iteratedFDeriv ℝ n ((fun z => u (x₀ + z)) ∘ A) y = _
  rw [A.iteratedFDeriv_comp_right hf y (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.smul_apply, A, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  simpa only [affineScale, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    using (iteratedFDeriv ℝ n u (x₀ + h • y)).map_smul_univ (fun _ => h) v

theorem iteratedFDeriv_affineScale_apply {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (x₀ : Plane) (h : ℝ) (n : ℕ) (y : Plane) (v : Fin n → Plane) :
    iteratedFDeriv ℝ n (u ∘ affineScale x₀ h) y v =
      (h ^ n : ℂ) * iteratedFDeriv ℝ n u (affineScale x₀ h y) v := by
  rw [iteratedFDeriv_affineScale hu]
  simp [Complex.real_smul]

theorem norm_iteratedFDeriv_affineScale {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (x₀ : Plane) (h : ℝ) (n : ℕ) (y : Plane) :
    ‖iteratedFDeriv ℝ n (u ∘ affineScale x₀ h) y‖ =
      |h| ^ n * ‖iteratedFDeriv ℝ n u (affineScale x₀ h y)‖ := by
  rw [iteratedFDeriv_affineScale hu, norm_smul, Real.norm_eq_abs, abs_pow]

theorem norm_iteratedFDeriv_affineScale_of_nonneg {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (x₀ : Plane) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) (y : Plane) :
    ‖iteratedFDeriv ℝ n (u ∘ affineScale x₀ h) y‖ =
      h ^ n * ‖iteratedFDeriv ℝ n u (affineScale x₀ h y)‖ := by
  rw [norm_iteratedFDeriv_affineScale hu, abs_of_nonneg hh]

theorem partialDerivative_affineScale {u : Wavefunction} (hu : Differentiable ℝ u)
    (x₀ : Plane) (h : ℝ) (i : Fin 2) (y : Plane) :
    partialDerivative i (u ∘ affineScale x₀ h) y =
      (h : ℂ) * partialDerivative i u (affineScale x₀ h y) := by
  have hd : HasFDerivAt (affineScale x₀ h)
      (h • ContinuousLinearMap.id ℝ Plane) y :=
    ((hasFDerivAt_id y).const_smul h).const_add x₀
  rw [partialDerivative, (hu (affineScale x₀ h y)).hasFDerivAt.comp y hd |>.fderiv]
  simp [partialDerivative, Complex.real_smul]

theorem partialDerivative_partialDerivative_affineScale {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (x₀ : Plane) (h : ℝ) (i j : Fin 2) (y : Plane) :
    partialDerivative i (partialDerivative j (u ∘ affineScale x₀ h)) y =
      (h ^ 2 : ℂ) * partialDerivative i (partialDerivative j u) (affineScale x₀ h y) := by
  have heq : partialDerivative j (u ∘ affineScale x₀ h) =
      (h : ℂ) • (partialDerivative j u ∘ affineScale x₀ h) := by
    funext z
    exact partialDerivative_affineScale (hu.differentiable (by simp)) x₀ h j z
  have hv := (contDiff_partialDerivative j hu).comp (contDiff_affineScale x₀ h)
  rw [heq, partialDerivative, fderiv_const_smul (hv.differentiable (by simp) y)]
  change (h : ℂ) * partialDerivative i (partialDerivative j u ∘ affineScale x₀ h) y = _
  rw [partialDerivative_affineScale ((contDiff_partialDerivative j hu).differentiable (by simp))]
  ring

end InfiniteZero
