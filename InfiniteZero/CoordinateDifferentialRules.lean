import InfiniteZero.MagneticTestGraph

/-!
# Elementary rules for coordinate derivatives

These identities are used when differentiating the local elliptic equation.
They apply to complex-valued functions with real coordinate derivatives.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

theorem partialDerivative_neg (i : Fin 2) (u : Wavefunction) :
    partialDerivative i (-u) = -partialDerivative i u := by
  ext x
  simp only [partialDerivative, Pi.neg_apply, fderiv_neg,
    ContinuousLinearMap.neg_apply]

theorem partialDerivative_sub (i : Fin 2) {u v : Wavefunction}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    partialDerivative i (u - v) = partialDerivative i u - partialDerivative i v := by
  rw [sub_eq_add_neg, partialDerivative_add i hu hv.neg, partialDerivative_neg,
    sub_eq_add_neg]

theorem partialDerivative_mul (i : Fin 2) {u v : Wavefunction}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    partialDerivative i (u * v) =
      partialDerivative i u * v + u * partialDerivative i v := by
  ext x
  change fderiv ℝ (fun y => u y * v y) x (coordinateVector i) = _
  rw [fderiv_fun_mul (hu x) (hv x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Pi.add_apply, Pi.mul_apply, partialDerivative]
  ring

theorem partialDerivative_sum {ι : Type*} (s : Finset ι) (i : Fin 2)
    {u : ι → Wavefunction} (hu : ∀ j ∈ s, Differentiable ℝ (u j)) :
    partialDerivative i (∑ j ∈ s, u j) = ∑ j ∈ s, partialDerivative i (u j) := by
  ext x
  simp only [partialDerivative, Finset.sum_apply]
  rw [fderiv_sum (fun j hj => hu j hj x)]
  simp only [ContinuousLinearMap.sum_apply]

/-- Equality on an open set can be differentiated at each of its points. -/
theorem partialDerivative_eqOn {s : Set Plane} (hs : IsOpen s)
    {u v : Wavefunction} (h : Set.EqOn u v s) (i : Fin 2) :
    Set.EqOn (partialDerivative i u) (partialDerivative i v) s := by
  intro x hx
  have he : u =ᶠ[nhds x] v := Filter.Eventually.mono (hs.mem_nhds hx) h
  exact congrArg (fun D : Plane →L[ℝ] ℂ => D (coordinateVector i)) he.fderiv_eq

end InfiniteZero
