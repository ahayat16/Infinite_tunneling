import InfiniteZero.ComplexCuspPhase
import InfiniteZero.ComplexCuspKernelHolomorphic
import InfiniteZero.CuspChartJacobian
import InfiniteZero.HoppingChannels

/-!
# Identification of the complex charts with the physical source kernel

Cartesian coordinates identify the polynomial complex charts at real normal
parameters with the actual cusp chart in the Euclidean plane and its reflection.
The bilinear radius there equals the physical Euclidean norm. Consequently
the actual source kernel is exactly the complex bridge kernel times its
polynomial magnetic phase, with the physical sign and normalization.

These are algebraic identities valid for all real parameters. They impose no
positivity or asymptotic hypotheses and contain no atomic source estimates.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

open Geometry

@[simp] theorem planeCartesianEquiv_reflection (x : Plane) :
    planeCartesianEquiv (reflection x) = Geometry.reflect (planeCartesianEquiv x) := by
  simp [planeCartesianEquiv_apply, reflection, Geometry.reflect]

/-- Real parameters in the complex upper chart give the actual physical chart. -/
theorem complexCuspPlus_eq_cuspChart (p : CuspParameters) (s t : ℝ) :
    complexCuspPlus p.R s (t : ℂ) =
      complexifyPoint (planeCartesianEquiv (p.cuspChart (t, s))) := by
  ext <;> simp [complexCuspPlus, polynomialCuspChart, complexifyPoint,
    planeCartesianEquiv_apply, cuspChart, cuspTip, cuspNormal, cuspTangent,
    tipPlus, normalPlus, tangentPlus]
  ring

/-- The lower complex chart is exactly the reflection used in the potential. -/
theorem complexCuspMinus_eq_reflection_cuspChart (p : CuspParameters) (r u : ℝ) :
    complexCuspMinus p.R r (u : ℂ) =
      complexifyPoint (planeCartesianEquiv (reflection (p.cuspChart (u, r)))) := by
  ext <;> simp [complexCuspMinus, polynomialCuspChart, complexifyPoint,
    planeCartesianEquiv_apply, reflection, cuspChart, cuspTip, cuspNormal, cuspTangent,
    tipMinus, normalMinus, tangentMinus] <;> ring

/-- The coordinate length is Euclidean, irrespective of the product-type norm. -/
theorem length_planeCartesianEquiv (x : Plane) :
    Geometry.length (planeCartesianEquiv x) = ‖x‖ := by
  simp [Geometry.length, Geometry.sqNorm, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs]

theorem complexRadius_planeCartesianEquiv (x : Plane) :
    complexRadius (complexifyPoint (planeCartesianEquiv x)) = (‖x‖ : ℂ) := by
  rw [complexRadius_complexifyPoint, length_planeCartesianEquiv]

theorem complexRadius_cuspPlus_real (p : CuspParameters) (s t : ℝ) :
    complexRadius (complexCuspPlus p.R s (t : ℂ)) = (‖p.cuspChart (t, s)‖ : ℂ) := by
  rw [complexCuspPlus_eq_cuspChart, complexRadius_planeCartesianEquiv]

theorem complexRadius_cuspMinus_real (p : CuspParameters) (r u : ℝ) :
    complexRadius (complexCuspMinus p.R r (u : ℂ)) =
      (‖reflection (p.cuspChart (u, r))‖ : ℂ) := by
  rw [complexCuspMinus_eq_reflection_cuspChart, complexRadius_planeCartesianEquiv]

/-- The bridge vector has the actual displacement and the same orientation. -/
theorem bridge_planeCartesianEquiv (L : ℝ) (z w : Plane) :
    Geometry.bridge L (planeCartesianEquiv z) (planeCartesianEquiv w) =
      planeCartesianEquiv (z + w - 2 • displacement L) := by
  ext <;> simp [Geometry.bridge, planeCartesianEquiv_apply, displacement, coordinateVector]

theorem complexBridge_planeCartesianEquiv (L : ℝ) (z w : Plane) :
    complexBridge L (complexifyPoint (planeCartesianEquiv z))
      (complexifyPoint (planeCartesianEquiv w)) =
        complexifyPoint (planeCartesianEquiv (z + w - 2 • displacement L)) := by
  rw [complexBridge_complexifyPoint, bridge_planeCartesianEquiv]

theorem complexRadius_bridge_planeCartesianEquiv (L : ℝ) (z w : Plane) :
    complexRadius (complexBridge L (complexifyPoint (planeCartesianEquiv z))
      (complexifyPoint (planeCartesianEquiv w))) =
        (‖z + w - 2 • displacement L‖ : ℂ) := by
  rw [complexBridge_planeCartesianEquiv, complexRadius_planeCartesianEquiv]

theorem complexRadius_cuspBridge_real (p : CuspParameters) (L s r t u : ℝ) :
    complexRadius (complexBridge L (complexCuspPlus p.R s (t : ℂ))
      (complexCuspMinus p.R r (u : ℂ))) =
        (‖p.cuspChart (t, s) + reflection (p.cuspChart (u, r)) - 2 • displacement L‖ : ℂ) := by
  rw [complexCuspPlus_eq_cuspChart, complexCuspMinus_eq_reflection_cuspChart,
    complexRadius_bridge_planeCartesianEquiv]

theorem sourcePhase_eq_phase (b L : ℝ) (z w : Plane) :
    sourcePhase b L z w = Geometry.phase b L (planeCartesianEquiv z) (planeCartesianEquiv w) := rfl

theorem complexPhase_planeCartesianEquiv (b L : ℝ) (z w : Plane) :
    complexPhase b L (complexifyPoint (planeCartesianEquiv z))
      (complexifyPoint (planeCartesianEquiv w)) = (sourcePhase b L z w : ℂ) := by
  rw [complexPhase_complexifyPoint, ← sourcePhase_eq_phase]

/-- Exact agreement with the physical source kernel for arbitrary physical points. -/
theorem sourceKernel_eq_complex (b L h E : ℝ) (z w : Plane) :
    sourceKernel b L h E z w =
      complexLandauKernel b h E
        (complexRadius (complexBridge L (complexifyPoint (planeCartesianEquiv z))
          (complexifyPoint (planeCartesianEquiv w)))) *
      Complex.exp (Complex.I * complexPhase b L (complexifyPoint (planeCartesianEquiv z))
        (complexifyPoint (planeCartesianEquiv w)) / (h : ℂ)) := by
  rw [complexRadius_bridge_planeCartesianEquiv, complexLandauKernel_ofReal,
    complexPhase_planeCartesianEquiv]
  unfold sourceKernel
  congr 1
  congr 1
  push_cast
  ring

theorem complexCuspPlusKernel_ofReal (p : CuspParameters) (b h E s t u : ℝ) :
    complexCuspPlusKernel b h E p.R s ((t : ℂ), (u : ℂ)) =
      (landauKernel b h E ‖p.cuspChart (t, s)‖ : ℂ) := by
  simp only [complexCuspPlusKernel, complexRadius_cuspPlus_real, complexLandauKernel_ofReal]

theorem complexCuspMinusKernel_ofReal (p : CuspParameters) (b h E r t u : ℝ) :
    complexCuspMinusKernel b h E p.R r ((t : ℂ), (u : ℂ)) =
      (landauKernel b h E ‖reflection (p.cuspChart (u, r))‖ : ℂ) := by
  simp only [complexCuspMinusKernel, complexRadius_cuspMinus_real, complexLandauKernel_ofReal]

theorem complexCuspBridgeKernel_ofReal (p : CuspParameters) (b h E L s r t u : ℝ) :
    complexCuspBridgeKernel b h E p.R L s r ((t : ℂ), (u : ℂ)) =
      (landauKernel b h E
        ‖p.cuspChart (t, s) + reflection (p.cuspChart (u, r)) - 2 • displacement L‖ : ℂ) := by
  simp only [complexCuspBridgeKernel, complexRadius_cuspBridge_real, complexLandauKernel_ofReal]

/-- The true source kernel on the two physical cusp charts is exactly the
holomorphic bridge kernel times the actual polynomial magnetic phase. -/
theorem sourceKernel_cuspChart_eq (p : CuspParameters) (b L h E s r t u : ℝ) :
    sourceKernel b L h E (p.cuspChart (t, s)) (reflection (p.cuspChart (u, r))) =
      complexCuspBridgeKernel b h E p.R L s r ((t : ℂ), (u : ℂ)) *
        Complex.exp (Complex.I * complexPhase b L (complexCuspPlus p.R s (t : ℂ))
          (complexCuspMinus p.R r (u : ℂ)) / (h : ℂ)) := by
  rw [sourceKernel_eq_complex, ← complexCuspPlus_eq_cuspChart,
    ← complexCuspMinus_eq_reflection_cuspChart]
  rfl

end InfiniteZero.CuspParameters
