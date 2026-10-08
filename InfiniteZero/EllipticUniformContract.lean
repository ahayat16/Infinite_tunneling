import InfiniteZero.EllipticSobolevContract

/-!
# Local contracts for the elliptic induction

The balls and coefficient bound are fixed before the coefficients and the
solution. These predicates organize the proof of the uniform estimate;
they introduce no admitted result.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- A common bound for ordered coordinate derivatives of the first- and
zeroth-order coefficients on the outer ball. -/
def EllipticCoefficientBound (n : ℕ) (R B : ℝ)
    (a : Fin 2 → Wavefunction) (q : Wavefunction) : Prop :=
  ∀ j : ℕ, j ≤ n → ∀ x ∈ Metric.ball (0 : Plane) R,
    ∀ α : Fin j → Fin 2,
    (∀ i, ‖iteratedFDeriv ℝ j (a i) x (fun k => coordinateVector (α k))‖ ≤ B) ∧
    ‖iteratedFDeriv ℝ j q x (fun k => coordinateVector (α k))‖ ≤ B

theorem EllipticCoefficientBound.mono_order {m n : ℕ} {R B : ℝ}
    {a : Fin 2 → Wavefunction} {q : Wavefunction}
    (h : EllipticCoefficientBound n R B a q) (hmn : m ≤ n) :
    EllipticCoefficientBound m R B a q := by
  intro j hj x hx α
  exact h j (hj.trans hmn) x hx α

theorem EllipticCoefficientBound.mono_radius {n : ℕ} {r R B : ℝ}
    {a : Fin 2 → Wavefunction} {q : Wavefunction}
    (h : EllipticCoefficientBound n R B a q) (hrR : r ≤ R) :
    EllipticCoefficientBound n r B a q := by
  intro j hj x hx α
  exact h j hj x (Metric.ball_subset_ball hrR hx) α

theorem EllipticCoefficientBound.values {n : ℕ} {R B : ℝ}
    {a : Fin 2 → Wavefunction} {q : Wavefunction}
    (h : EllipticCoefficientBound n R B a q) {x : Plane}
    (hx : x ∈ Metric.ball (0 : Plane) R) :
    (∀ i, ‖a i x‖ ≤ B) ∧ ‖q x‖ ≤ B := by
  simpa only [iteratedFDeriv_zero_apply] using h 0 (Nat.zero_le n) x hx Fin.elim0

/-- Uniform local gain of two derivatives at one fixed order. The two
radii may vary, but their choice precedes all coefficient and solution data. -/
def HasLocalCoordinateEllipticEstimate (n : ℕ) : Prop :=
  ∀ r R : ℝ, 0 < r → r < R → ∀ B : ℝ, 0 ≤ B → ∃ C > 0,
    ∀ (a : Fin 2 → Wavefunction) (q u f : Wavefunction),
    (∀ i, ContDiff ℝ ∞ (a i)) → ContDiff ℝ ∞ q →
    ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
    EllipticCoefficientBound n R B a q →
    (∀ x ∈ Metric.ball (0 : Plane) R, ellipticExpression a q u x = f x) →
    coordinateSobolevNorm (n + 2) r u ≤
      C * (coordinateSobolevNorm 0 R u + coordinateSobolevNorm n R f)

end InfiniteZero
