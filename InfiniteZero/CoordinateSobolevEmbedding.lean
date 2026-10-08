import InfiniteZero.CoordinateSobolevCalculus
import InfiniteZero.EllipticSobolevContract

/-!
# Higher-order point evaluation from the scalar H² estimate

The only analytic input in this reduction is point evaluation at the
centre of the unit ball for a smooth complex function in `H²`. Applying
that estimate to coordinate derivatives gives all higher-order versions.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

/-- Point evaluation at the centre of the unit ball is bounded by the
local `H²` norm in dimension two. -/
def HasH2PointEvaluation : Prop :=
  ∃ C > 0, ∀ u : Wavefunction, ContDiff ℝ ∞ u →
    ‖u 0‖ ≤ C * coordinateSobolevNorm 2 1 u

/-- An ordered derivative consumes its order in the local Sobolev norm. -/
theorem coordinateSobolevNorm_coordinateDerivative_le {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) {j : ℕ} (α : Fin j → Fin 2) (n : ℕ) (r : ℝ) :
    coordinateSobolevNorm n r (coordinateDerivative α u) ≤
      coordinateSobolevNorm (n + j) r u := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    have heq : coordinateDerivative α u =
        coordinateDerivative (Fin.init α) (partialDerivative (α (Fin.last j)) u) := by
      rw [coordinateDerivative_partialDerivative hu, Fin.snoc_init_self]
    rw [heq]
    calc
      _ ≤ coordinateSobolevNorm (n + j) r (partialDerivative (α (Fin.last j)) u) :=
        ih (contDiff_partialDerivative _ hu) (Fin.init α)
      _ ≤ coordinateSobolevNorm (n + (j + 1)) r u := by
        simpa only [Nat.add_assoc] using
          coordinateSobolevNorm_partialDerivative_le hu (n + j) r (α (Fin.last j))

/-- The order-zero `H²` point estimate implies the full coordinate
Sobolev embedding contract, with the same constant at every order. -/
theorem coordinateSobolevEmbedding_of_h2_pointEvaluation
    (h : HasH2PointEvaluation) : HasCoordinateSobolevEmbedding := by
  obtain ⟨C, hC, hpoint⟩ := h
  intro n
  refine ⟨C, hC, ?_⟩
  intro u hu j hj α
  change ‖coordinateDerivative α u 0‖ ≤ C * coordinateSobolevNorm (n + 2) 1 u
  calc
    _ ≤ C * coordinateSobolevNorm 2 1 (coordinateDerivative α u) :=
      hpoint _ (contDiff_coordinateDerivative hu α)
    _ ≤ C * coordinateSobolevNorm (2 + j) 1 u :=
      mul_le_mul_of_nonneg_left (coordinateSobolevNorm_coordinateDerivative_le hu α 2 1) hC.le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (coordinateSobolevNorm_mono_order (by omega) 1 u) hC.le

end InfiniteZero
