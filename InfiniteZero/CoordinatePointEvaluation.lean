import InfiniteZero.CoordinateRectangleFTC
import InfiniteZero.UnitMeasureL2Bound
import InfiniteZero.CoordinateSobolevEmbedding
import InfiniteZero.CoordinateSobolevProduct

/-!
# The H² point estimate in two dimensions

Two applications of the fundamental theorem of calculus and the
Cauchy–Schwarz inequality prove point evaluation for a function supported
inside the unit ball. A fixed smooth cutoff and the proved Sobolev
multiplication estimate extend this to every smooth function.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace InfiniteZero

/-- A compactly supported smooth function inside the unit ball satisfies
the point estimate with constant one. -/
theorem norm_zero_le_coordinateSobolevNorm_two_of_support {u : Wavefunction}
    (hu : IsTestFunction u) (hs : tsupport u ⊆ Metric.ball (0 : Plane) 1) :
    ‖u 0‖ ≤ coordinateSobolevNorm 2 1 u := by
  let D := partialDerivative 1 (partialDerivative 0 u)
  have hD : IsTestFunction D := (hu.partialDerivative 0).partialDerivative 1
  let F : (ℝ × ℝ) → ℂ := fun q => D (cartesianPoint q.1 q.2)
  have hFI : Integrable F volume :=
    CuspParameters.planeCartesianEquiv_symm_measurePreserving.integrable_comp_of_integrable
      (hD.1.continuous.integrable_of_hasCompactSupport hD.2)
  have hF2 : Integrable (fun q => ‖F q‖ ^ 2) volume :=
    CuspParameters.planeCartesianEquiv_symm_measurePreserving.integrable_comp_of_integrable
      hD.integrable_norm_sq
  have hμ : (volume.restrict negativeUnitSquare) Set.univ = 1 := by
    simp only [Measure.restrict_apply_univ, volume_negativeUnitSquare]
  have hpoint := norm_integral_sq_le_integral_norm_sq_of_measure_univ_eq_one hμ
    hFI.integrableOn hF2.integrableOn
  have heq : u 0 = ∫ q in negativeUnitSquare, F q := value_zero_eq_integral_mixed_square hu.1 hs
  rw [← heq] at hpoint
  have hfull : (∫ q in negativeUnitSquare, ‖F q‖ ^ 2) ≤
      ∫ x : Plane, ‖D x‖ ^ 2 := by
    calc
      _ ≤ ∫ q : ℝ × ℝ, ‖F q‖ ^ 2 :=
        setIntegral_le_integral hF2 (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      _ = _ := CuspParameters.planeCartesianEquiv_symm_measurePreserving.integral_comp
        CuspParameters.planeCartesianEquiv.symm.toHomeomorph.measurableEmbedding
        (fun x : Plane => ‖D x‖ ^ 2)
  have hsD : tsupport D ⊆ Metric.ball (0 : Plane) 1 :=
    (tsupport_partialDerivative_subset _ 1).trans
      ((tsupport_partialDerivative_subset _ 0).trans hs)
  have hmass : (∫ x : Plane, ‖D x‖ ^ 2) = coordinateSobolevNorm 0 1 D ^ 2 := by
    rw [coordinateSobolevNorm_zero, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsD h))]
      simp).symm
  have hnorm : coordinateSobolevNorm 0 1 D ≤ coordinateSobolevNorm 2 1 u :=
    (coordinateSobolevNorm_partialDerivative_le (hu.partialDerivative 0).1 0 1 1).trans
      (coordinateSobolevNorm_partialDerivative_le hu.1 1 1 0)
  have hsq := hpoint.trans hfull
  rw [hmass] at hsq
  have hm0 := coordinateSobolevNorm_nonneg 0 1 D
  have hm2 := coordinateSobolevNorm_nonneg 2 1 u
  nlinarith [norm_nonneg (u 0)]

/-- All jets of a fixed compactly supported smooth coefficient admit a
common finite bound through any prescribed order. -/
theorem exists_coordinateJet_bound_of_isTestFunction {a : Wavefunction}
    (ha : IsTestFunction a) (n : ℕ) :
    ∃ B > 0, ∀ j : ℕ, j ≤ n → ∀ x : Plane, ∀ α : Fin j → Fin 2,
      ‖coordinateDerivative α a x‖ ≤ B := by
  classical
  have hj : ∀ j : Fin (n + 1), ∃ B : ℝ, ∀ x : Plane,
      ‖iteratedFDeriv ℝ j.val a x‖ ≤ B := by
    intro j
    exact (ha.2.iteratedFDeriv j.val).exists_bound_of_continuous
      ((contDiff_infty.mp ha.1 j.val).continuous_iteratedFDeriv le_rfl)
  choose bounds hb using hj
  let B := 1 + ∑ j : Fin (n + 1), |bounds j|
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro j hj x α
  let k : Fin (n + 1) := ⟨j, by omega⟩
  have hk : |bounds k| ≤ ∑ l : Fin (n + 1), |bounds l| :=
    Finset.single_le_sum (fun l _ => abs_nonneg (bounds l)) (Finset.mem_univ k)
  have hbB : bounds k ≤ B := by dsimp [B]; linarith [le_abs_self (bounds k)]
  exact (coordinate_tensor_component_le _ α).trans ((hb k x).trans hbB)

/-- Point evaluation in local `H²(B₁)` in dimension two, proved using
only a smooth cutoff, the fundamental theorem, and Cauchy–Schwarz. -/
theorem coordinateH2PointEvaluation : HasH2PointEvaluation := by
  obtain ⟨χ, hχ, hc, _hχ01, hone, hs, _hgradient⟩ :=
    exists_elliptic_cutoff (r := 1 / 2) (R := 1) (by norm_num) (by norm_num)
  let η : Wavefunction := fun x => (χ x : ℂ)
  have hη : IsTestFunction η :=
    ⟨Complex.ofRealCLM.contDiff.comp hχ,
      hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)⟩
  have hηs : tsupport η ⊆ Metric.ball (0 : Plane) 1 :=
    (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) (by simp) χ).trans hs
  obtain ⟨B, hB, hbound⟩ := exists_coordinateJet_bound_of_isTestFunction hη 2
  obtain ⟨K, hK, hmul⟩ := coordinateSobolevNorm_mul_estimate 2
  refine ⟨K * B, mul_pos hK hB, ?_⟩
  intro u hu
  have hv : IsTestFunction (fun x => η x * u x) := ⟨hη.1.mul hu, hη.2.mul_right⟩
  have hvs : tsupport (fun x => η x * u x) ⊆ Metric.ball (0 : Plane) 1 :=
    tsupport_mul_subset_left.trans hηs
  have hη0 : η 0 = 1 := by
    simp only [η, hone 0 (by simp), Complex.ofReal_one]
  calc
    ‖u 0‖ = ‖η 0 * u 0‖ := by rw [hη0, one_mul]
    _ ≤ coordinateSobolevNorm 2 1 (fun x => η x * u x) :=
      norm_zero_le_coordinateSobolevNorm_two_of_support hv hvs
    _ ≤ K * B * coordinateSobolevNorm 2 1 u :=
      hmul hη.1 hu hB.le (fun j hj x _ α => hbound j hj x α)

end InfiniteZero
