import InfiniteZero.ParityTrialStates

/-!
# Covariance of the actual test-function form

Magnetic translation and inversion preserve smooth compactly supported
functions. Simultaneous magnetic translation preserves the physical scalar
product, and translating or reflecting the potential together with the test
function preserves its quadratic energy. The inverse translation is exact,
including its magnetic phase.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem IsTestFunction.magneticTranslated {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) (b coupling : ℝ) (a : Plane) :
    IsTestFunction (magneticTranslation b coupling a ψ) := by
  refine ⟨contDiff_magneticTranslation b coupling a hψ.1, ?_⟩
  have hs : HasCompactSupport (fun x => ψ (x - a)) :=
    hψ.2.comp_homeomorph (Homeomorph.subRight a)
  exact hs.mul_left

theorem IsTestFunction.inversion {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    IsTestFunction (fun x => ψ (-x)) :=
  ⟨hψ.1.comp contDiff_id.neg, hψ.2.comp_homeomorph (Homeomorph.neg Plane)⟩

theorem magneticTranslation_neg_cancel (b coupling : ℝ) (a : Plane) (ψ : Wavefunction) :
    magneticTranslation b coupling (-a) (magneticTranslation b coupling a ψ) = ψ := by
  funext x
  have hneg : wedge x (-a) = -wedge x a := by simp [wedge]; ring
  have hadd : wedge (x + a) a = wedge x a := by simp [wedge]; ring
  simp only [magneticTranslation, sub_neg_eq_add, add_sub_cancel_right, hneg, hadd]
  rw [← mul_assoc, ← Complex.exp_add]
  have he : -Complex.I * ((b * coupling / 2 * -wedge x a : ℝ) : ℂ) +
      -Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [he, Complex.exp_zero, one_mul]

theorem magneticTranslation_cancel_neg (b coupling : ℝ) (a : Plane) (ψ : Wavefunction) :
    magneticTranslation b coupling a (magneticTranslation b coupling (-a) ψ) = ψ := by
  simpa only [neg_neg] using magneticTranslation_neg_cancel b coupling (-a) ψ

theorem waveInner_magneticTranslation (b coupling : ℝ) (a : Plane)
    (φ ψ : Wavefunction) :
    waveInner (magneticTranslation b coupling a φ) (magneticTranslation b coupling a ψ) =
      waveInner φ ψ := by
  have hpoint (x : Plane) :
      star (magneticTranslation b coupling a φ x) * magneticTranslation b coupling a ψ x =
        star (φ (x - a)) * ψ (x - a) := by
    let z := Complex.exp (-Complex.I * ((b * coupling / 2 * wedge x a : ℝ) : ℂ))
    have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp, Complex.mul_re]
    have hzprod : star z * z = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, hz]
      norm_num
    change star (z * φ (x - a)) * (z * ψ (x - a)) = _
    calc
      _ = (star z * z) * (star (φ (x - a)) * ψ (x - a)) := by
        simp only [star_mul']
        ring
      _ = _ := by rw [hzprod, one_mul]
  simp only [waveInner, hpoint]
  exact integral_sub_right_eq_self (fun x => star (φ x) * ψ x) a

theorem magneticForm_magneticTranslation (b coupling : ℝ) (a : Plane) (V : Potential)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    magneticForm b coupling (fun x => V (x - a)) (magneticTranslation b coupling a ψ) =
      magneticForm b coupling V ψ := by
  simp only [magneticForm,
    covariantDerivative_magneticTranslation b coupling a _ (hψ.1.differentiable (by simp)),
    norm_magneticTranslation]
  exact integral_sub_right_eq_self
    (fun x => (∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2) +
      coupling ^ 2 * V x * ‖ψ x‖ ^ 2) a

theorem magneticForm_inversion (b coupling : ℝ) (V : Potential)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    magneticForm b coupling (fun x => V (-x)) (fun x => ψ (-x)) =
      magneticForm b coupling V ψ := by
  simp only [magneticForm,
    covariantDerivative_inversion b coupling _ (hψ.1.differentiable (by simp)), norm_neg]
  exact integral_neg_eq_self
    (fun x => (∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2) +
      coupling ^ 2 * V x * ‖ψ x‖ ^ 2) volume

end InfiniteZero
