import InfiniteZero.CoordinateDifferentialRules
import InfiniteZero.LaplacianHessianEnergy
import InfiniteZero.EllipticInteriorContract

/-!
# Differentiating the local elliptic equation

One coordinate derivative of a solution satisfies the same equation with
a new source. Its additional terms use one derivative of the coefficients
and at most one derivative of the original solution. Iterating this identity
is the finite-order elliptic bootstrap.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

theorem coordinateLaplacian_partialDerivative {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (i : Fin 2) :
    coordinateLaplacian (partialDerivative i u) =
      partialDerivative i (coordinateLaplacian u) := by
  have hrepr : coordinateLaplacian u =
      ∑ j : Fin 2, partialDerivative j (partialDerivative j u) := by
    ext x
    simp [coordinateLaplacian]
  rw [hrepr, partialDerivative_sum Finset.univ i (fun j _ =>
    (contDiff_partialDerivative j (contDiff_partialDerivative j hu)).differentiable (by simp))]
  ext x
  simp only [coordinateLaplacian, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [partialDerivative_comm (contDiff_partialDerivative j hu) i j,
    partialDerivative_comm hu i j]

theorem ellipticExpression_eq_coordinateLaplacian (a : Fin 2 → Wavefunction)
    (q u : Wavefunction) :
    ellipticExpression a q u = -coordinateLaplacian u +
      (∑ j : Fin 2, a j * partialDerivative j u) + q * u := by
  ext x
  simp [ellipticExpression, coordinateLaplacian]

theorem contDiff_ellipticExpression {a : Fin 2 → Wavefunction} {q u : Wavefunction}
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hq : ContDiff ℝ ∞ q) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (ellipticExpression a q u) := by
  rw [ellipticExpression_eq_coordinateLaplacian]
  simpa only [Finset.sum_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply] using
    ((contDiff_coordinateLaplacian hu).neg.add
      (ContDiff.sum (s := Finset.univ) fun j _ =>
        (ha j).mul (contDiff_partialDerivative j hu))).add (hq.mul hu)

/-- Source in the differentiated equation. The coefficients in the
principal equation remain `a,q`; coefficient derivatives occur only here. -/
def ellipticDerivativeSource (i : Fin 2) (a : Fin 2 → Wavefunction)
    (q u f : Wavefunction) : Wavefunction :=
  partialDerivative i f - (∑ j : Fin 2, partialDerivative i (a j) * partialDerivative j u) -
    partialDerivative i q * u

theorem contDiff_ellipticDerivativeSource (i : Fin 2) {a : Fin 2 → Wavefunction}
    {q u f : Wavefunction} (ha : ∀ j, ContDiff ℝ ∞ (a j))
    (hq : ContDiff ℝ ∞ q) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ellipticDerivativeSource i a q u f) := by
  simpa only [ellipticDerivativeSource, Finset.sum_apply, Pi.sub_apply, Pi.mul_apply] using
    ((contDiff_partialDerivative i hf).sub
      (ContDiff.sum (s := Finset.univ) fun j _ => (contDiff_partialDerivative i (ha j)).mul
        (contDiff_partialDerivative j hu))).sub ((contDiff_partialDerivative i hq).mul hu)

/-- Exact differentiated equation, before restricting to any ball. -/
theorem ellipticExpression_partialDerivative (i : Fin 2) {a : Fin 2 → Wavefunction}
    {q u : Wavefunction} (ha : ∀ j, ContDiff ℝ ∞ (a j))
    (hq : ContDiff ℝ ∞ q) (hu : ContDiff ℝ ∞ u) :
    ellipticExpression a q (partialDerivative i u) =
      ellipticDerivativeSource i a q u (ellipticExpression a q u) := by
  have hD (j : Fin 2) := contDiff_partialDerivative j hu
  have hsum : ContDiff ℝ ∞ (∑ j : Fin 2, a j * partialDerivative j u) :=
    by simpa only [Finset.sum_apply, Pi.mul_apply] using
      ContDiff.sum (s := Finset.univ) (fun j _ => (ha j).mul (hD j))
  have hqu : ContDiff ℝ ∞ (q * u) := hq.mul hu
  have hleft : ContDiff ℝ ∞ (-coordinateLaplacian u +
      ∑ j : Fin 2, a j * partialDerivative j u) :=
    (contDiff_coordinateLaplacian hu).neg.add hsum
  unfold ellipticDerivativeSource
  rw [ellipticExpression_eq_coordinateLaplacian a q u,
    partialDerivative_add i (hleft.differentiable (by simp))
      (hqu.differentiable (by simp)),
    partialDerivative_add i (ψ := -coordinateLaplacian u)
      ((contDiff_coordinateLaplacian hu).neg.differentiable (by simp))
      (hsum.differentiable (by simp)), partialDerivative_neg,
    ← coordinateLaplacian_partialDerivative hu i,
    partialDerivative_sum Finset.univ i (u := fun j => a j * partialDerivative j u)
      (fun j _ => ((ha j).mul (hD j)).differentiable (by simp)),
    partialDerivative_mul i (hq.differentiable (by simp)) (hu.differentiable (by simp))]
  simp_rw [partialDerivative_mul i ((ha _).differentiable (by simp))
    ((hD _).differentiable (by simp))]
  rw [ellipticExpression_eq_coordinateLaplacian]
  ext x
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
    partialDerivative_comm hu i 0, partialDerivative_comm hu i 1]
  ring

/-- The differentiated equation holds on the same open ball. -/
theorem ellipticExpression_partialDerivative_on_ball (i : Fin 2)
    {a : Fin 2 → Wavefunction} {q u f : Wavefunction} {R : ℝ}
    (ha : ∀ j, ContDiff ℝ ∞ (a j)) (hq : ContDiff ℝ ∞ q) (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x ∈ Metric.ball (0 : Plane) R, ellipticExpression a q u x = f x) :
    ∀ x ∈ Metric.ball (0 : Plane) R,
      ellipticExpression a q (partialDerivative i u) x = ellipticDerivativeSource i a q u f x := by
  intro x hx
  rw [ellipticExpression_partialDerivative i ha hq hu]
  unfold ellipticDerivativeSource
  simp only [Pi.sub_apply]
  rw [partialDerivative_eqOn Metric.isOpen_ball heq i hx]

end InfiniteZero
