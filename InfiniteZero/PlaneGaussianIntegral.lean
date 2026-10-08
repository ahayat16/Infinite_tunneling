import InfiniteZero.MagneticModel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Group.Integral

/-!
# Gaussian integration on the Euclidean plane

The planar volume normalization gives mass `π/a` for `exp(-a|x|²)`.
Translations and reflections preserve this integral.
-/
noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem integrable_planeGaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Plane => Real.exp (-a * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (a : ℂ)) ha 0 (0 : Plane)).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

theorem integral_planeGaussian {a : ℝ} (ha : 0 < a) :
    (∫ x : Plane, Real.exp (-a * ‖x‖ ^ 2)) = Real.pi / a := by
  simpa [Plane] using
    (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Plane) ha)

theorem integrable_planeGaussian_sub {a : ℝ} (ha : 0 < a) (x : Plane) :
    Integrable (fun y : Plane => Real.exp (-a * ‖x - y‖ ^ 2)) :=
  (integrable_planeGaussian ha).comp_sub_left x

theorem integral_planeGaussian_sub {a : ℝ} (ha : 0 < a) (x : Plane) :
    (∫ y : Plane, Real.exp (-a * ‖x - y‖ ^ 2)) = Real.pi / a := by
  rw [integral_sub_left_eq_self (fun y : Plane => Real.exp (-a * ‖y‖ ^ 2)) volume x,
    integral_planeGaussian ha]

end InfiniteZero
