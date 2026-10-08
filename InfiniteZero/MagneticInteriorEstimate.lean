import InfiniteZero.RescaledMagneticCoefficientBounds
import InfiniteZero.AffineScaleL2

/-!
# Applying the fixed-ball classical estimate to the magnetic equation

Coefficient bounds and the exact affine change of variables are proved in
Lean. Only the universal fixed-ball interior estimate is an explicit input.
The loss in dimension two is one inverse length, independently of jet order
when semiclassical derivatives are used.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem exists_magnetic_interior_jet_bound
    (hInterior : HasInteriorEllipticEstimate) (b : ℝ) (V : Potential)
    (hV : ContDiff ℝ ∞ V) (n : ℕ) (R Benergy : ℝ) :
    ∃ C > 0, ∀ coupling : ℝ, 1 ≤ coupling → ∀ E : ℝ,
      |(coupling⁻¹) ^ 2 * E| ≤ Benergy → ∀ x₀ : Plane, ‖x₀‖ ≤ R →
      ∀ u f : Wavefunction, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
      (∀ x : Plane, (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        (magneticHamiltonian b coupling V u x - (E : ℂ) * u x) = f x) →
      ∀ U F : ℝ, 0 ≤ U → 0 ≤ F →
      (∫ x in Metric.ball x₀ (2 * coupling⁻¹), ‖u x‖ ^ 2) ≤ U ^ 2 →
      (∀ j : ℕ, j ≤ n → ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
        (∫ x in Metric.ball x₀ (2 * coupling⁻¹),
          ‖((coupling⁻¹) ^ j : ℂ) * iteratedFDeriv ℝ j f x v‖ ^ 2) ≤ F ^ 2) →
      ∀ j : ℕ, j ≤ n →
        (coupling⁻¹) ^ j * ‖iteratedFDeriv ℝ j u x₀‖ ≤ C * coupling * (U + F) := by
  obtain ⟨B, hB, hcoeff⟩ := exists_rescaledMagneticCoefficient_jet_bound b V hV n R Benergy
  obtain ⟨C, hC, hestimate⟩ := hInterior n B hB.le
  refine ⟨C, hC, ?_⟩
  intro coupling hc E hE x₀ hx₀ u f hu hf heq U F hU hF huMass hfMass j hj
  have hcpos : 0 < coupling := lt_of_lt_of_le zero_lt_one hc
  have hhpos : 0 < coupling⁻¹ := inv_pos.mpr hcpos
  have hh : coupling⁻¹ ∈ Icc (0 : ℝ) 1 :=
    ⟨hhpos.le, inv_le_one_of_one_le₀ hc⟩
  have hlocalCoeffs : ∀ k : ℕ, k ≤ n → ∀ y ∈ Metric.ball (0 : Plane) 2,
      (∀ i, ‖iteratedFDeriv ℝ k (rescaledMagneticFirstOrder b x₀ coupling⁻¹ i) y‖ ≤ B) ∧
      ‖iteratedFDeriv ℝ k
        (rescaledMagneticZerothOrder b V ((coupling⁻¹) ^ 2 * E) x₀ coupling⁻¹) y‖ ≤ B := by
    intro k hk y hy
    exact hcoeff coupling⁻¹ hh x₀ hx₀ ((coupling⁻¹) ^ 2 * E) hE k hk y
      (Metric.ball_subset_closedBall hy)
  have huScaled : (∫ y in Metric.ball (0 : Plane) 2,
      ‖(u ∘ affineScale x₀ coupling⁻¹) y‖ ^ 2) ≤ (coupling * U) ^ 2 := by
    rw [show (fun y => ‖(u ∘ affineScale x₀ coupling⁻¹) y‖ ^ 2) =
      (fun y => ‖u (affineScale x₀ coupling⁻¹ y)‖ ^ 2) from rfl,
      setIntegral_norm_sq_affineScale_ball_two u x₀ hhpos, inv_inv]
    exact (mul_le_mul_of_nonneg_left huMass (sq_nonneg coupling)).trans_eq (by ring)
  have hfScaled : ∀ k : ℕ, k ≤ n → ∀ v : Fin k → Plane, (∀ i, ‖v i‖ ≤ 1) →
      (∫ y in Metric.ball (0 : Plane) 2,
        ‖iteratedFDeriv ℝ k (f ∘ affineScale x₀ coupling⁻¹) y v‖ ^ 2) ≤
          (coupling * F) ^ 2 := by
    intro k hk v hv
    calc
      _ = ∫ y in Metric.ball (0 : Plane) 2,
          ‖((coupling⁻¹) ^ k : ℂ) * iteratedFDeriv ℝ k f (affineScale x₀ coupling⁻¹ y) v‖ ^ 2 := by
        apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        intro y _
        dsimp only
        rw [iteratedFDeriv_affineScale_apply hf]
      _ = coupling ^ 2 * ∫ x in Metric.ball x₀ (2 * coupling⁻¹),
          ‖((coupling⁻¹) ^ k : ℂ) * iteratedFDeriv ℝ k f x v‖ ^ 2 := by
        simpa only [inv_inv] using setIntegral_norm_sq_affineScale_ball_two
          (fun x => ((coupling⁻¹) ^ k : ℂ) * iteratedFDeriv ℝ k f x v) x₀ hhpos
      _ ≤ coupling ^ 2 * F ^ 2 :=
        mul_le_mul_of_nonneg_left (hfMass k hk v hv) (sq_nonneg coupling)
      _ = _ := by ring
  have hjet := hestimate (rescaledMagneticFirstOrder b x₀ coupling⁻¹)
    (rescaledMagneticZerothOrder b V ((coupling⁻¹) ^ 2 * E) x₀ coupling⁻¹)
    (u ∘ affineScale x₀ coupling⁻¹) (f ∘ affineScale x₀ coupling⁻¹)
    (fun i => contDiff_rescaledMagneticFirstOrder b x₀ coupling⁻¹ i)
    (contDiff_rescaledMagneticZerothOrder b hV _ x₀ coupling⁻¹)
    (hu.comp (contDiff_affineScale x₀ coupling⁻¹))
    (hf.comp (contDiff_affineScale x₀ coupling⁻¹)) hlocalCoeffs
    (fun y _ => magneticEquation_affineScale b coupling E V hu hcpos.ne' heq x₀ y)
    (coupling * U) (coupling * F) (mul_nonneg hcpos.le hU) (mul_nonneg hcpos.le hF)
    huScaled hfScaled j hj
  rw [norm_iteratedFDeriv_affineScale_of_nonneg hu x₀ hhpos.le,
    affineScale, smul_zero, add_zero] at hjet
  exact hjet.trans_eq (by ring)

end InfiniteZero
