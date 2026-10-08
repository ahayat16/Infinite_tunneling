import InfiniteZero.CoordinateSobolevCalculus

/-!
# Multiplication in local coordinate Sobolev norms

A coefficient whose coordinate derivatives through order `n` are bounded
acts boundedly on the local `H^n` norm. The constant depends only on `n`;
the proof consists of the finite Leibniz rule and Cauchy–Schwarz.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

private def jetNormSum (n : ℕ) (u : Wavefunction) (x : Plane) : ℝ :=
  ∑ α : CoordinateJetIndex n, ‖coordinateDerivative α.2 u x‖

private theorem jetNormSum_nonneg (n : ℕ) (u : Wavefunction) (x : Plane) :
    0 ≤ jetNormSum n u x := Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem tensor_norm_le_jetNormSum {j n : ℕ} (hj : j ≤ n)
    (u : Wavefunction) (x : Plane) : ‖iteratedFDeriv ℝ j u x‖ ≤ jetNormSum n u x := by
  calc
    _ ≤ ∑ α : Fin j → Fin 2, ‖coordinateDerivative α u x‖ :=
      tensor_norm_le_coordinate_sum _
    _ ≤ ∑ k : Fin (n + 1), ∑ α : Fin k.val → Fin 2,
        ‖coordinateDerivative α u x‖ := by
      exact Finset.single_le_sum
        (f := fun k : Fin (n + 1) => ∑ α : Fin k.val → Fin 2, ‖coordinateDerivative α u x‖)
        (fun k _ => Finset.sum_nonneg fun α _ => norm_nonneg (coordinateDerivative α u x))
        (Finset.mem_univ (⟨j, by omega⟩ : Fin (n + 1)))
    _ = _ := by unfold jetNormSum; rw [Fintype.sum_sigma]

private theorem jetNormSum_sq_le (n : ℕ) (u : Wavefunction) (x : Plane) :
    jetNormSum n u x ^ 2 ≤ coordinateJetCount n *
      ∑ α : CoordinateJetIndex n, ‖coordinateDerivative α.2 u x‖ ^ 2 := by
  simpa only [jetNormSum, one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, coordinateJetCount] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (CoordinateJetIndex n))
      (fun _ => (1 : ℝ)) (fun α => ‖coordinateDerivative α.2 u x‖)

private def productLeibnizConstant (n : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * 2 ^ i

private theorem productLeibnizConstant_pos (n : ℕ) : 0 < productLeibnizConstant n := by
  unfold productLeibnizConstant
  positivity

private theorem le_productLeibnizConstant {j n : ℕ} (hj : j ≤ n) :
    (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * 2 ^ i) ≤
      productLeibnizConstant n := by
  have h : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * 2 ^ i) ≤
      ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * 2 ^ i :=
    Finset.single_le_sum
      (f := fun k : ℕ => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * 2 ^ i)
      (fun k _ => Finset.sum_nonneg fun i _ => by positivity)
      (Finset.mem_range.mpr (show j < n + 1 by omega))
  unfold productLeibnizConstant
  linarith

private theorem coordinateDerivative_mul_le {n j : ℕ} (hj : j ≤ n)
    {a u : Wavefunction} (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u)
    {B : ℝ} (hB : 0 ≤ B) (x : Plane)
    (hcoeff : ∀ k : ℕ, k ≤ n → ∀ α : Fin k → Fin 2,
      ‖coordinateDerivative α a x‖ ≤ B) (α : Fin j → Fin 2) :
    ‖coordinateDerivative α (fun y => a y * u y) x‖ ≤
      productLeibnizConstant n * B * jetNormSum n u x := by
  have hsum := jetNormSum_nonneg n u x
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => a y * u y) x‖ := coordinate_tensor_component_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i a x‖ * ‖iteratedFDeriv ℝ (j - i) u x‖ :=
      norm_iteratedFDeriv_mul_le (contDiff_infty.mp ha j) (contDiff_infty.mp hu j) x le_rfl
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (2 ^ i * B) * jetNormSum n u x := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (tensor_norm_le_of_coordinate_bound _ (hcoeff i hin)) (Nat.cast_nonneg _)
      · exact tensor_norm_le_jetNormSum ((Nat.sub_le j i).trans hj) u x
      · exact norm_nonneg _
      · positivity
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * 2 ^ i) * B *
        jetNormSum n u x := by simp_rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_productLeibnizConstant hj) hB) hsum

/-- Multiplication by a coefficient with bounded coordinate jets preserves
local `H^n`, uniformly over the radius and the coefficient. -/
theorem coordinateSobolevNorm_mul_estimate (n : ℕ) :
    ∃ K > 0, ∀ {a u : Wavefunction}, ContDiff ℝ ∞ a → ContDiff ℝ ∞ u →
      ∀ {B r : ℝ}, 0 ≤ B →
      (∀ j : ℕ, j ≤ n → ∀ x ∈ Metric.ball (0 : Plane) r,
        ∀ α : Fin j → Fin 2, ‖coordinateDerivative α a x‖ ≤ B) →
      coordinateSobolevNorm n r (fun x => a x * u x) ≤
        K * B * coordinateSobolevNorm n r u := by
  classical
  let K := productLeibnizConstant n
  have hK : 0 < K := productLeibnizConstant_pos n
  have hN := coordinateJetCount_nonneg n
  refine ⟨K * (coordinateJetCount n + 1), mul_pos hK (by linarith), ?_⟩
  intro a u ha hu B r hB hcoeff
  have huI (α : CoordinateJetIndex n) := integrableOn_coordinateDerivative_sq hu α.2 r
  have hpoint (α : CoordinateJetIndex n) (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) r) :
      ‖coordinateDerivative α.2 (fun y => a y * u y) x‖ ^ 2 ≤
        (K * B) ^ 2 * coordinateJetCount n *
          ∑ β : CoordinateJetIndex n, ‖coordinateDerivative β.2 u x‖ ^ 2 := by
    calc
      _ ≤ (K * B * jetNormSum n u x) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _)
          (coordinateDerivative_mul_le (Nat.le_of_lt_succ α.1.isLt) ha hu hB x
            (fun j hj β => hcoeff j hj x hx β) α.2) 2
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left (jetNormSum_sq_le n u x) (sq_nonneg (K * B))]
  have hmass (α : CoordinateJetIndex n) :
      (∫ x in Metric.ball (0 : Plane) r,
        ‖coordinateDerivative α.2 (fun y => a y * u y) x‖ ^ 2) ≤
      (K * B) ^ 2 * coordinateJetCount n * coordinateSobolevNorm n r u ^ 2 := by
    rw [coordinateSobolevNorm_sq, ← integral_finsetSum _ (fun α _ => huI α),
      ← integral_const_mul]
    exact setIntegral_mono_on (integrableOn_coordinateDerivative_sq (ha.mul hu) α.2 r)
      ((integrable_finsetSum _ (fun α _ => huI α)).const_mul _) measurableSet_ball
      (hpoint α)
  have htotal : coordinateSobolevNorm n r (fun x => a x * u x) ^ 2 ≤
      (K * coordinateJetCount n * B * coordinateSobolevNorm n r u) ^ 2 := by
    rw [coordinateSobolevNorm_sq]
    calc
      _ ≤ ∑ _α : CoordinateJetIndex n,
          (K * B) ^ 2 * coordinateJetCount n * coordinateSobolevNorm n r u ^ 2 :=
        Finset.sum_le_sum fun α _ => hmass α
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; unfold coordinateJetCount; ring
  have hu0 := coordinateSobolevNorm_nonneg n r u
  have hprod : 0 ≤ K * coordinateJetCount n * B * coordinateSobolevNorm n r u := by positivity
  have hnorm : coordinateSobolevNorm n r (fun x => a x * u x) ≤
      K * coordinateJetCount n * B * coordinateSobolevNorm n r u := by
    nlinarith [coordinateSobolevNorm_nonneg n r (fun x => a x * u x)]
  calc
    _ ≤ _ := hnorm
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hK.le hB) hu0]

end InfiniteZero
