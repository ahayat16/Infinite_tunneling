import InfiniteZero.EllipticCoordinateNorms
import InfiniteZero.MagneticCovariance
import InfiniteZero.WeightedLocalMassComparison
import InfiniteZero.SemiclassicalLeibniz

/-!
# Calculus of local coordinate Sobolev norms

The identities below retain the ordered-coordinate convention of
`coordinateSobolevNorm`. They provide the elementary calculus used in
interior elliptic estimates.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- The derivative in an ordered list of coordinate directions. -/
def coordinateDerivative {j : ℕ} (α : Fin j → Fin 2) (u : Wavefunction) : Wavefunction :=
  fun x => iteratedFDeriv ℝ j u x (fun i => coordinateVector (α i))

theorem contDiff_coordinateDerivative {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    {j : ℕ} (α : Fin j → Fin 2) : ContDiff ℝ ∞ (coordinateDerivative α u) := by
  have hj : ContDiff ℝ ∞ (iteratedFDeriv ℝ j u) :=
    hu.iteratedFDeriv_right le_rfl
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Plane) ℂ
    (fun i => coordinateVector (α i))).contDiff.comp hj

theorem integrableOn_coordinateDerivative_sq {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    {j : ℕ} (α : Fin j → Fin 2) (r : ℝ) :
    IntegrableOn (fun x => ‖coordinateDerivative α u x‖ ^ 2) (Metric.ball (0 : Plane) r) :=
  continuous_integrableOn_norm_sq_ball (contDiff_coordinateDerivative hu α).continuous 0 r

@[simp] theorem coordinateDerivative_zero (α : Fin 0 → Fin 2) (u : Wavefunction) :
    coordinateDerivative α u = u := rfl

theorem coordinateDerivative_partialDerivative {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    {j : ℕ} (α : Fin j → Fin 2) (i : Fin 2) :
    coordinateDerivative α (partialDerivative i u) =
      coordinateDerivative (Fin.snoc α i) u := by
  funext x
  change iteratedFDeriv ℝ j (fun y => fderiv ℝ u y (coordinateVector i)) x _ = _
  rw [iteratedFDeriv_clm_apply_const_apply (contDiff_infty.mp (hu.fderiv_right (m := ∞) le_rfl) j) le_rfl]
  rw [coordinateDerivative, iteratedFDeriv_succ_apply_right]
  congr 2
  · ext k
    simp [Fin.init]
  · simp

/-- The squared local norm is the sum of the masses of its coordinate jets. -/
theorem coordinateSobolevNorm_sq (n : ℕ) (r : ℝ) (u : Wavefunction) :
    coordinateSobolevNorm n r u ^ 2 =
      ∑ α : CoordinateJetIndex n,
        ∫ x in Metric.ball (0 : Plane) r, ‖coordinateDerivative α.2 u x‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

theorem coordinateSobolevNorm_sq_eq_sum_range (n : ℕ) (r : ℝ) (u : Wavefunction) :
    coordinateSobolevNorm n r u ^ 2 =
      ∑ j ∈ Finset.range (n + 1), ∑ α : Fin j → Fin 2,
        ∫ x in Metric.ball (0 : Plane) r, ‖coordinateDerivative α u x‖ ^ 2 := by
  rw [coordinateSobolevNorm_sq, Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range
    (fun j => ∑ α : Fin j → Fin 2,
      ∫ x in Metric.ball (0 : Plane) r, ‖coordinateDerivative α u x‖ ^ 2) (n + 1)

@[simp] theorem coordinateSobolevNorm_zero (r : ℝ) (u : Wavefunction) :
    coordinateSobolevNorm 0 r u = Real.sqrt (∫ x in Metric.ball (0 : Plane) r, ‖u x‖ ^ 2) := by
  simp [coordinateSobolevNorm, Fintype.sum_sigma]
  rfl

theorem coordinateSobolevNorm_mono_order {n m : ℕ} (hnm : n ≤ m)
    (r : ℝ) (u : Wavefunction) : coordinateSobolevNorm n r u ≤ coordinateSobolevNorm m r u := by
  have hs : coordinateSobolevNorm n r u ^ 2 ≤ coordinateSobolevNorm m r u ^ 2 := by
    rw [coordinateSobolevNorm_sq_eq_sum_range, coordinateSobolevNorm_sq_eq_sum_range]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
  nlinarith [coordinateSobolevNorm_nonneg n r u, coordinateSobolevNorm_nonneg m r u]

theorem coordinateSobolevNorm_mono_radius {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (n : ℕ) {r R : ℝ} (hrR : r ≤ R) :
    coordinateSobolevNorm n r u ≤ coordinateSobolevNorm n R u := by
  have hs : coordinateSobolevNorm n r u ^ 2 ≤ coordinateSobolevNorm n R u ^ 2 := by
    rw [coordinateSobolevNorm_sq, coordinateSobolevNorm_sq]
    apply Finset.sum_le_sum
    intro α _
    exact setIntegral_mono_set (integrableOn_coordinateDerivative_sq hu α.2 R)
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun _ hx => Metric.ball_subset_ball hrR hx)
  nlinarith [coordinateSobolevNorm_nonneg n r u, coordinateSobolevNorm_nonneg n R u]

/-- Splitting a nonempty coordinate list at its last entry gives the exact
first-derivative recursion for the squared local Sobolev norm. -/
theorem coordinateSobolevNorm_succ_sq {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (r : ℝ) :
    coordinateSobolevNorm (n + 1) r u ^ 2 = coordinateSobolevNorm 0 r u ^ 2 +
      ∑ i : Fin 2, coordinateSobolevNorm n r (partialDerivative i u) ^ 2 := by
  classical
  simp only [coordinateSobolevNorm_sq_eq_sum_range]
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_add, Finset.sum_range_one, Fintype.sum_unique, coordinateDerivative_zero]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← (Fin.snocEquiv (fun _ : Fin (j + 1) => Fin 2)).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro α _
  rw [coordinateDerivative_partialDerivative hu]
  rfl

/-- Differentiation consumes one order of the local Sobolev norm. -/
theorem coordinateSobolevNorm_partialDerivative_le {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (r : ℝ) (i : Fin 2) :
    coordinateSobolevNorm n r (partialDerivative i u) ≤ coordinateSobolevNorm (n + 1) r u := by
  have hi : coordinateSobolevNorm n r (partialDerivative i u) ^ 2 ≤
      ∑ k : Fin 2, coordinateSobolevNorm n r (partialDerivative k u) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (coordinateSobolevNorm n r (partialDerivative k u))) (Finset.mem_univ i)
  have heq := coordinateSobolevNorm_succ_sq hu n r
  nlinarith [sq_nonneg (coordinateSobolevNorm 0 r u),
    coordinateSobolevNorm_nonneg n r (partialDerivative i u),
    coordinateSobolevNorm_nonneg (n + 1) r u]

/-- A convenient unsquared form of the exact first-derivative recursion. -/
theorem coordinateSobolevNorm_succ_le {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (r : ℝ) :
    coordinateSobolevNorm (n + 1) r u ≤ coordinateSobolevNorm 0 r u +
      ∑ i : Fin 2, coordinateSobolevNorm n r (partialDerivative i u) := by
  have heq := coordinateSobolevNorm_succ_sq hu n r
  simp only [Fin.sum_univ_two] at heq ⊢
  have h0 := coordinateSobolevNorm_nonneg 0 r u
  have h1 := coordinateSobolevNorm_nonneg n r (partialDerivative 0 u)
  have h2 := coordinateSobolevNorm_nonneg n r (partialDerivative 1 u)
  nlinarith [coordinateSobolevNorm_nonneg (n + 1) r u,
    mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

theorem coordinateSobolevNorm_one_sq {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (r : ℝ) :
    coordinateSobolevNorm 1 r u ^ 2 =
      (∫ x in Metric.ball (0 : Plane) r, ‖u x‖ ^ 2) +
      ∑ i : Fin 2, ∫ x in Metric.ball (0 : Plane) r, ‖partialDerivative i u x‖ ^ 2 := by
  rw [coordinateSobolevNorm_succ_sq hu 0]
  simp only [coordinateSobolevNorm_zero]
  simp only [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

theorem coordinateDerivative_add {u v : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) {j : ℕ} (α : Fin j → Fin 2) :
    coordinateDerivative α (u + v) = coordinateDerivative α u + coordinateDerivative α v := by
  funext x
  simp only [coordinateDerivative, Pi.add_apply]
  rw [iteratedFDeriv_add_apply (contDiff_infty.mp hu j).contDiffAt
    (contDiff_infty.mp hv j).contDiffAt, ContinuousMultilinearMap.add_apply]

/-- A coarse triangle inequality, sufficient for estimates with an unspecified constant. -/
theorem coordinateSobolevNorm_add_le {u v : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (n : ℕ) (r : ℝ) :
    coordinateSobolevNorm n r (u + v) ≤
      2 * (coordinateSobolevNorm n r u + coordinateSobolevNorm n r v) := by
  have hsq : coordinateSobolevNorm n r (u + v) ^ 2 ≤
      2 * (coordinateSobolevNorm n r u ^ 2 + coordinateSobolevNorm n r v ^ 2) := by
    simp only [coordinateSobolevNorm_sq]
    rw [Finset.sum_add_distrib.symm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    have huI := integrableOn_coordinateDerivative_sq hu α.2 r
    have hvI := integrableOn_coordinateDerivative_sq hv α.2 r
    rw [← integral_add huI hvI, ← integral_const_mul]
    apply setIntegral_mono_on (integrableOn_coordinateDerivative_sq (hu.add hv) α.2 r)
      ((huI.add hvI).const_mul 2) measurableSet_ball
    intro x _
    change ‖coordinateDerivative α.2 (u + v) x‖ ^ 2 ≤
      2 * (‖coordinateDerivative α.2 u x‖ ^ 2 + ‖coordinateDerivative α.2 v x‖ ^ 2)
    rw [coordinateDerivative_add hu hv, Pi.add_apply]
    have h := norm_add_le (coordinateDerivative α.2 u x) (coordinateDerivative α.2 v x)
    nlinarith [norm_nonneg (coordinateDerivative α.2 u x),
      norm_nonneg (coordinateDerivative α.2 v x),
      norm_nonneg (coordinateDerivative α.2 u x + coordinateDerivative α.2 v x),
      sq_nonneg (‖coordinateDerivative α.2 u x‖ - ‖coordinateDerivative α.2 v x‖)]
  have hu0 := coordinateSobolevNorm_nonneg n r u
  have hv0 := coordinateSobolevNorm_nonneg n r v
  nlinarith [coordinateSobolevNorm_nonneg n r (u + v), mul_nonneg hu0 hv0,
    sq_nonneg (coordinateSobolevNorm n r u), sq_nonneg (coordinateSobolevNorm n r v)]

@[simp] theorem coordinateSobolevNorm_neg (n : ℕ) (r : ℝ) (u : Wavefunction) :
    coordinateSobolevNorm n r (-u) = coordinateSobolevNorm n r u := by
  simp only [coordinateSobolevNorm, iteratedFDeriv_neg_apply,
    ContinuousMultilinearMap.neg_apply, norm_neg]

theorem coordinateSobolevNorm_sub_le {u v : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (n : ℕ) (r : ℝ) :
    coordinateSobolevNorm n r (u - v) ≤
      2 * (coordinateSobolevNorm n r u + coordinateSobolevNorm n r v) := by
  simpa only [sub_eq_add_neg, coordinateSobolevNorm_neg] using
    coordinateSobolevNorm_add_le (u := u) (v := -v) hu hv.neg n r

end InfiniteZero
