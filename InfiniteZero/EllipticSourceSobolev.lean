import InfiniteZero.CoordinateSobolevProduct
import InfiniteZero.EllipticDifferentiation
import InfiniteZero.EllipticUniformContract

/-!
# Uniform bounds for the source in the differentiated elliptic equation

Leibniz estimates control the new source by one additional derivative of
the original source and solution. The constants depend only on the order
and the common coefficient bound.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem EllipticCoefficientBound.coordinate_derivative {n : ℕ} {R B : ℝ}
    {a : Fin 2 → Wavefunction} {q : Wavefunction}
    (ha : ∀ k, ContDiff ℝ ∞ (a k)) (hq : ContDiff ℝ ∞ q)
    (h : EllipticCoefficientBound (n + 1) R B a q) (i : Fin 2) :
    EllipticCoefficientBound n R B (fun k => partialDerivative i (a k))
      (partialDerivative i q) := by
  intro j hj x hx α
  have hb := h (j + 1) (by omega) x hx (Fin.snoc α i)
  constructor
  · intro k
    change ‖coordinateDerivative α (partialDerivative i (a k)) x‖ ≤ B
    rw [coordinateDerivative_partialDerivative (ha k)]
    exact hb.1 k
  · change ‖coordinateDerivative α (partialDerivative i q) x‖ ≤ B
    rw [coordinateDerivative_partialDerivative hq]
    exact hb.2

/-- Uniform bound for the first differentiated source. Its constant is
chosen before the radius, coefficients, source and solution. -/
theorem ellipticDerivativeSource_sobolev_bound (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ D > 0, ∀ (R : ℝ) (a : Fin 2 → Wavefunction) (q u f : Wavefunction),
      (∀ j, ContDiff ℝ ∞ (a j)) → ContDiff ℝ ∞ q →
      ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
      EllipticCoefficientBound (n + 1) R B a q → ∀ i : Fin 2,
      coordinateSobolevNorm n R (ellipticDerivativeSource i a q u f) ≤
        D * (coordinateSobolevNorm (n + 1) R f + coordinateSobolevNorm (n + 1) R u) := by
  obtain ⟨K, hK, hmul⟩ := coordinateSobolevNorm_mul_estimate n
  refine ⟨4 + 18 * K * B, by positivity, ?_⟩
  intro R a q u f ha hq hu hf hcoeff i
  have hderiv := hcoeff.coordinate_derivative ha hq i
  let P := K * B * coordinateSobolevNorm (n + 1) R u
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (mul_nonneg hK.le hB) (coordinateSobolevNorm_nonneg _ _ _)
  let p : Fin 2 → Wavefunction := fun j => partialDerivative i (a j) * partialDerivative j u
  let z : Wavefunction := partialDerivative i q * u
  have hp (j : Fin 2) : ContDiff ℝ ∞ (p j) :=
    (contDiff_partialDerivative i (ha j)).mul (contDiff_partialDerivative j hu)
  have hz : ContDiff ℝ ∞ z := (contDiff_partialDerivative i hq).mul hu
  have hpbound (j : Fin 2) : coordinateSobolevNorm n R (p j) ≤ P := by
    have hb := hmul (contDiff_partialDerivative i (ha j))
      (contDiff_partialDerivative j hu) hB
      (fun k hk x hx α => (hderiv k hk x hx α).1 j)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (coordinateSobolevNorm_partialDerivative_le hu n R j) (mul_nonneg hK.le hB))
  have hzbound : coordinateSobolevNorm n R z ≤ P := by
    have hb := hmul (contDiff_partialDerivative i hq) hu hB
      (fun k hk x hx α => (hderiv k hk x hx α).2)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (coordinateSobolevNorm_mono_order (Nat.le_succ n) R u) (mul_nonneg hK.le hB))
  have hsum : coordinateSobolevNorm n R (p 0 + p 1) ≤ 4 * P := by
    have h := coordinateSobolevNorm_add_le (hp 0) (hp 1) n R
    linarith [hpbound 0, hpbound 1]
  have hfbound := coordinateSobolevNorm_partialDerivative_le hf n R i
  have hfirst := coordinateSobolevNorm_sub_le (u := partialDerivative i f) (v := p 0 + p 1)
    (contDiff_partialDerivative i hf)
    ((hp 0).add (hp 1)) n R
  have hlast := coordinateSobolevNorm_sub_le
    (u := partialDerivative i f - (p 0 + p 1)) (v := z)
    ((contDiff_partialDerivative i hf).sub ((hp 0).add (hp 1))) hz n R
  have hsmall : coordinateSobolevNorm n R (ellipticDerivativeSource i a q u f) ≤
      4 * coordinateSobolevNorm (n + 1) R f + 18 * P := by
    simp only [ellipticDerivativeSource, Fin.sum_univ_two]
    change coordinateSobolevNorm n R (partialDerivative i f - (p 0 + p 1) - z) ≤ _
    linarith
  refine hsmall.trans ?_
  dsimp [P]
  nlinarith [coordinateSobolevNorm_nonneg (n + 1) R f,
    coordinateSobolevNorm_nonneg (n + 1) R u,
    mul_nonneg (mul_nonneg hK.le hB) (coordinateSobolevNorm_nonneg (n + 1) R f)]

end InfiniteZero
