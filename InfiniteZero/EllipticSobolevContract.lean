import InfiniteZero.EllipticCoordinateNorms

/-!
# Interior Sobolev estimates and embedding

These two contracts use the usual integer-order Sobolev norm in coordinate
derivatives. The first is the local gain of two derivatives for a fixed
Laplacian with smooth complex lower-order coefficients. The second is
Sobolev embedding on a ball in dimension two. Conversion to the directional
jet formulation used in the magnetic estimates is proved separately.
`EllipticUniformInterior` proves the first contract. The second is derived
from the point-evaluation input isolated in `CoordinateSobolevEmbedding`.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- The standard interior `H^(n+2)` estimate on nested fixed balls, uniform
under bounds on coordinate derivatives of the lower-order coefficients
through order `n`. The `L²` term on the right removes any requirement of
coercivity or a sign for the complex zeroth-order coefficient. -/
def HasCoordinateInteriorSobolevEstimate : Prop :=
  ∀ n : ℕ, ∀ B : ℝ, 0 ≤ B → ∃ C > 0,
    ∀ (a : Fin 2 → Wavefunction) (q u f : Wavefunction),
    (∀ i, ContDiff ℝ ∞ (a i)) → ContDiff ℝ ∞ q →
    ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
    (∀ j : ℕ, j ≤ n → ∀ x ∈ Metric.ball (0 : Plane) 2,
      ∀ α : Fin j → Fin 2,
      (∀ i, ‖iteratedFDeriv ℝ j (a i) x (fun k => coordinateVector (α k))‖ ≤ B) ∧
      ‖iteratedFDeriv ℝ j q x (fun k => coordinateVector (α k))‖ ≤ B) →
    (∀ x ∈ Metric.ball (0 : Plane) 2, ellipticExpression a q u x = f x) →
    coordinateSobolevNorm (n + 2) 1 u ≤
      C * (Real.sqrt (∫ x in Metric.ball (0 : Plane) 2, ‖u x‖ ^ 2) +
        coordinateSobolevNorm n 2 f)

/-- The point-evaluation consequence of `H^(n+2)(B₁) ↪ C^n(B₁)` in
dimension two, expressed for coordinate derivatives of smooth functions. -/
def HasCoordinateSobolevEmbedding : Prop :=
  ∀ n : ℕ, ∃ C > 0, ∀ u : Wavefunction, ContDiff ℝ ∞ u →
    ∀ j : ℕ, j ≤ n → ∀ α : Fin j → Fin 2,
      ‖iteratedFDeriv ℝ j u 0 (fun k => coordinateVector (α k))‖ ≤
        C * coordinateSobolevNorm (n + 2) 1 u

end InfiniteZero
