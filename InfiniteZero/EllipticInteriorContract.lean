import InfiniteZero.MagneticModel
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A classical interior estimate on one fixed Euclidean ball

This is only a contract. Its principal part is exactly minus the Laplacian;
the lower-order coefficients can be complex. The constant is uniform over
all coefficients whose jets through the chosen order have one fixed bound.
No magnetic parameter, semiclassical scale, weight or potential occurs here.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- The fixed-principal-part elliptic expression used after rescaling. -/
def ellipticExpression (a : Fin 2 → Wavefunction) (q u : Wavefunction) : Wavefunction :=
  fun x => -(∑ i : Fin 2, partialDerivative i (partialDerivative i u) x) +
    (∑ i : Fin 2, a i x * partialDerivative i u x) + q x * u x

/-- Classical interior elliptic regularity followed by Sobolev embedding
in dimension two. Smoothness ensures every integral on the fixed ball is
finite. The hypotheses on all unit-direction jets in particular control
the finitely many coordinate derivatives needed by the Sobolev estimate.
The constant absorbs their number and depends only on `n` and `B`. -/
def HasInteriorEllipticEstimate : Prop :=
  ∀ n : ℕ, ∀ B : ℝ, 0 ≤ B → ∃ C > 0,
    ∀ (a : Fin 2 → Wavefunction) (q u f : Wavefunction),
    (∀ i, ContDiff ℝ ∞ (a i)) → ContDiff ℝ ∞ q →
    ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
    (∀ j : ℕ, j ≤ n → ∀ x ∈ Metric.ball (0 : Plane) 2,
      (∀ i, ‖iteratedFDeriv ℝ j (a i) x‖ ≤ B) ∧
      ‖iteratedFDeriv ℝ j q x‖ ≤ B) →
    (∀ x ∈ Metric.ball (0 : Plane) 2, ellipticExpression a q u x = f x) →
    ∀ U F : ℝ, 0 ≤ U → 0 ≤ F →
    (∫ x in Metric.ball (0 : Plane) 2, ‖u x‖ ^ 2) ≤ U ^ 2 →
    (∀ j : ℕ, j ≤ n → ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
      (∫ x in Metric.ball (0 : Plane) 2, ‖iteratedFDeriv ℝ j f x v‖ ^ 2) ≤ F ^ 2) →
    ∀ j : ℕ, j ≤ n → ‖iteratedFDeriv ℝ j u 0‖ ≤ C * (U + F)

end InfiniteZero
