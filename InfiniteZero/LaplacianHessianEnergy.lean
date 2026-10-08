import InfiniteZero.MagneticTestGraph
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Euclidean Laplacian and the Hessian energy identity

For smooth compactly supported complex-valued functions, integration by
parts identifies the squared `L²` norm of the Laplacian with the sum of
the squared `L²` norms of all ordered second coordinate derivatives.
These identities require no elliptic regularity input.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace InfiniteZero

/-- The Euclidean Laplacian, with the sign convention `Δ = ∂₀² + ∂₁²`. -/
def coordinateLaplacian (u : Wavefunction) : Wavefunction :=
  fun x => ∑ i : Fin 2, partialDerivative i (partialDerivative i u) x

/-- Mixed coordinate derivatives commute for smooth functions. -/
theorem partialDerivative_comm {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (i j : Fin 2) :
    partialDerivative i (partialDerivative j u) =
      partialDerivative j (partialDerivative i u) := by
  funext x
  have hdd : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hdd.differentiable (by simp)) x
  change fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector j)) x (coordinateVector i) =
    fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector i)) x (coordinateVector j)
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinateVector j)),
    fderiv_clm_apply hd (differentiableAt_const (coordinateVector i))]
  simpa using (hu.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField];
        exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq
    (coordinateVector i) (coordinateVector j)

theorem contDiff_coordinateLaplacian {u : Wavefunction} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (coordinateLaplacian u) := by
  unfold InfiniteZero.coordinateLaplacian
  exact ContDiff.sum fun i _ => contDiff_partialDerivative i (contDiff_partialDerivative i hu)

theorem IsTestFunction.coordinateLaplacian {u : Wavefunction} (hu : IsTestFunction u) :
    IsTestFunction (coordinateLaplacian u) := by
  have h := ((hu.partialDerivative 0).partialDerivative 0).add
    ((hu.partialDerivative 1).partialDerivative 1)
  unfold InfiniteZero.coordinateLaplacian
  simpa only [Fin.sum_univ_two, Pi.add_def] using h

/-- Two integrations by parts turn a mixed diagonal inner product into
the nonnegative energy of the corresponding Hessian entry. -/
theorem waveInner_diagonal_second_eq_hessian_mass {u : Wavefunction}
    (hu : IsTestFunction u) (i j : Fin 2) :
    waveInner (partialDerivative i (partialDerivative i u))
      (partialDerivative j (partialDerivative j u)) =
        (mass (partialDerivative i (partialDerivative j u)) : ℂ) := by
  have hi := hu.partialDerivative i
  have hj := hu.partialDerivative j
  have hjj := hj.partialDerivative j
  have hij := hj.partialDerivative i
  calc
    waveInner (partialDerivative i (partialDerivative i u))
        (partialDerivative j (partialDerivative j u)) =
      -waveInner (partialDerivative i u)
        (partialDerivative i (partialDerivative j (partialDerivative j u))) := by
          rw [waveInner_partialDerivative i hi hjj, neg_neg]
    _ = -waveInner (partialDerivative i u)
        (partialDerivative j (partialDerivative i (partialDerivative j u))) := by
          rw [partialDerivative_comm hj.1 i j]
    _ = waveInner (partialDerivative j (partialDerivative i u))
        (partialDerivative i (partialDerivative j u)) := by
          rw [waveInner_partialDerivative j hi hij, neg_neg]
    _ = (mass (partialDerivative i (partialDerivative j u)) : ℂ) := by
          rw [partialDerivative_comm hu.1 j i, waveInner_self_eq_mass]

/-- The compact-support Hessian identity, stated with the project's `mass`. -/
theorem laplacian_mass_eq_sum_hessian_mass {u : Wavefunction} (hu : IsTestFunction u) :
    mass (coordinateLaplacian u) =
      ∑ i : Fin 2, ∑ j : Fin 2, mass (partialDerivative i (partialDerivative j u)) := by
  have hD (i : Fin 2) := (hu.partialDerivative i).partialDerivative i
  have hinner : waveInner (coordinateLaplacian u) (coordinateLaplacian u) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        waveInner (partialDerivative i (partialDerivative i u))
          (partialDerivative j (partialDerivative j u)) := by
    unfold waveInner coordinateLaplacian
    simp only [star_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        (hD i).integrable_star_mul (hD j).1.continuous))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ =>
      (hD i).integrable_star_mul (hD j).1.continuous)]
  rw [waveInner_self_eq_mass] at hinner
  simp_rw [waveInner_diagonal_second_eq_hessian_mass hu] at hinner
  exact_mod_cast hinner

/-- Explicit integral form of the compact-support Hessian identity. -/
theorem sum_hessian_energy_eq_laplacian_energy {u : Wavefunction} (hu : IsTestFunction u) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      ∫ x, ‖partialDerivative i (partialDerivative j u) x‖ ^ 2) =
        ∫ x, ‖∑ i : Fin 2, partialDerivative i (partialDerivative i u) x‖ ^ 2 :=
  (laplacian_mass_eq_sum_hessian_mass hu).symm

/-- The Laplacian is negative semidefinite on compactly supported tests. -/
theorem waveInner_coordinateLaplacian {u : Wavefunction} (hu : IsTestFunction u) :
    waveInner u (coordinateLaplacian u) =
      -(∑ i : Fin 2, (mass (partialDerivative i u) : ℂ)) := by
  unfold waveInner coordinateLaplacian
  simp only [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    hu.integrable_star_mul ((hu.partialDerivative i).partialDerivative i).1.continuous)]
  change (∑ i : Fin 2, waveInner u (partialDerivative i (partialDerivative i u))) = _
  simp_rw [waveInner_partialDerivative _ hu (hu.partialDerivative _), waveInner_self_eq_mass]
  simp only [Finset.sum_neg_distrib]

end InfiniteZero
