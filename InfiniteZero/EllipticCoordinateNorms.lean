import InfiniteZero.EllipticInteriorContract
import InfiniteZero.RealRadialState
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Coordinate derivatives and local Sobolev norms

The coordinate Sobolev norm below is a finite sum of the squared `L²`
norms of ordered coordinate derivatives. Repeated multi-indices occur
with their multinomial multiplicity; this is an equivalent standard
integer-order Sobolev norm. The comparison with directional jets and
the operator norm of a derivative tensor is proved here.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- An ordered coordinate derivative of order at most `n`. -/
abbrev CoordinateJetIndex (n : ℕ) := Σ j : Fin (n + 1), Fin j.val → Fin 2

/-- Local `H^n` norm using all ordered coordinate derivatives. -/
def coordinateSobolevNorm (n : ℕ) (r : ℝ) (u : Wavefunction) : ℝ :=
  Real.sqrt (∑ α : CoordinateJetIndex n,
    ∫ x in Metric.ball (0 : Plane) r,
      ‖iteratedFDeriv ℝ α.1.val u x (fun i => coordinateVector (α.2 i))‖ ^ 2)

/-- The finite number of coordinate derivatives through order `n`. -/
def coordinateJetCount (n : ℕ) : ℝ := Fintype.card (CoordinateJetIndex n)

theorem coordinateJetCount_nonneg (n : ℕ) : 0 ≤ coordinateJetCount n := by
  unfold coordinateJetCount
  positivity

theorem coordinateSobolevNorm_nonneg (n : ℕ) (r : ℝ) (u : Wavefunction) :
    0 ≤ coordinateSobolevNorm n r u := Real.sqrt_nonneg _

/-- Every coordinate component is bounded by the operator norm of the tensor. -/
theorem coordinate_tensor_component_le {j : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) ℂ)
    (α : Fin j → Fin 2) : ‖T (fun i => coordinateVector (α i))‖ ≤ ‖T‖ := by
  simpa only [norm_coordinateVector, Finset.prod_const_one, mul_one] using
    T.le_opNorm (fun i => coordinateVector (α i))

/-- A tensor's operator norm is at most the sum of the norms of its coordinate
components. This explicit comparison works for order zero as well. -/
theorem tensor_norm_le_coordinate_sum {j : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) ℂ) :
    ‖T‖ ≤ ∑ α : Fin j → Fin 2, ‖T (fun i => coordinateVector (α i))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hrepr (x : Plane) : (∑ k : Fin 2, x k • coordinateVector k) = x := by
    ext k
    fin_cases k <;> simp [Fin.sum_univ_two, coordinateVector]
  have hexpand : T v = ∑ α : Fin j → Fin 2,
      (∏ i : Fin j, v i (α i)) • T (fun i => coordinateVector (α i)) := by
    calc
      T v = T (fun i => ∑ k : Fin 2, v i k • coordinateVector k) := by
        congr 1
        funext i
        exact (hrepr (v i)).symm
      _ = _ := by
        simpa only [ContinuousMultilinearMap.coe_coe, T.map_smul_univ] using
          T.toMultilinearMap.map_sum (fun (i : Fin j) (k : Fin 2) => v i k • coordinateVector k)
  rw [hexpand]
  calc
    ‖∑ α : Fin j → Fin 2,
        (∏ i : Fin j, v i (α i)) • T (fun i => coordinateVector (α i))‖
        ≤ ∑ α : Fin j → Fin 2,
          ‖(∏ i : Fin j, v i (α i)) • T (fun i => coordinateVector (α i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ α : Fin j → Fin 2,
          (∏ i : Fin j, ‖v i‖) * ‖T (fun i => coordinateVector (α i))‖ := by
      apply Finset.sum_le_sum
      intro α _
      rw [norm_smul, norm_prod]
      exact mul_le_mul_of_nonneg_right
        (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => PiLp.norm_apply_le (v i) (α i))) (norm_nonneg _)
    _ = (∑ α : Fin j → Fin 2, ‖T (fun i => coordinateVector (α i))‖) *
          ∏ i : Fin j, ‖v i‖ := by rw [← Finset.mul_sum, mul_comm]

/-- A common coordinate bound controls the operator norm, with explicit
factor `2^j` in the plane. -/
theorem tensor_norm_le_of_coordinate_bound {j : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) ℂ)
    {K : ℝ} (h : ∀ α : Fin j → Fin 2,
      ‖T (fun i => coordinateVector (α i))‖ ≤ K) : ‖T‖ ≤ 2 ^ j * K := by
  calc
    ‖T‖ ≤ ∑ α : Fin j → Fin 2, ‖T (fun i => coordinateVector (α i))‖ :=
      tensor_norm_le_coordinate_sum T
    _ ≤ ∑ _α : Fin j → Fin 2, K := Finset.sum_le_sum fun α _ => h α
    _ = 2 ^ j * K := by simp

/-- Bounds for every unit-direction derivative imply a local Sobolev bound
with the square root of the number of coordinate derivatives. -/
theorem coordinateSobolevNorm_le_of_directional_bounds (n : ℕ) (r : ℝ)
    (f : Wavefunction) {F : ℝ} (hF : 0 ≤ F)
    (hf : ∀ j : ℕ, j ≤ n → ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
      (∫ x in Metric.ball (0 : Plane) r, ‖iteratedFDeriv ℝ j f x v‖ ^ 2) ≤ F ^ 2) :
    coordinateSobolevNorm n r f ≤ Real.sqrt (coordinateJetCount n) * F := by
  unfold coordinateSobolevNorm
  calc
    Real.sqrt (∑ α : CoordinateJetIndex n,
        ∫ x in Metric.ball (0 : Plane) r,
          ‖iteratedFDeriv ℝ α.1.val f x (fun i => coordinateVector (α.2 i))‖ ^ 2)
        ≤ Real.sqrt (∑ _α : CoordinateJetIndex n, F ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun α _ =>
        hf α.1.val (Nat.le_of_lt_succ α.1.isLt)
          (fun i => coordinateVector (α.2 i)) (fun i => (norm_coordinateVector _).le)
    _ = Real.sqrt (coordinateJetCount n) * F := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change Real.sqrt (coordinateJetCount n * F ^ 2) = _
      rw [Real.sqrt_mul (coordinateJetCount_nonneg n), Real.sqrt_sq hF]

end InfiniteZero
