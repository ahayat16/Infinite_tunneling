import InfiniteZero.MagneticModel
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Weighted semiclassical jets of genuine wavefunctions

The weight is multiplied after differentiation. Linearity therefore needs
smoothness only of the wavefunctions, not of the weight.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

def weightedSemiclassicalJet (T : Plane → ℝ) (h κ : ℝ) (u : Wavefunction)
    (n : ℕ) (v : Fin n → Plane) : Wavefunction :=
  fun x => (Real.exp (κ / h * T x) : ℂ) * (h ^ n : ℂ) *
    iteratedFDeriv ℝ n u x v

theorem weightedSemiclassicalJet_continuous {T : Plane → ℝ} (hT : Continuous T)
    (h κ : ℝ) {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (v : Fin n → Plane) :
    Continuous (weightedSemiclassicalJet T h κ u n v) := by
  have hjet := ((contDiff_infty.mp hu n).continuous_iteratedFDeriv le_rfl).eval_const v
  have hweight : Continuous (fun x => (Real.exp (κ / h * T x) : ℂ)) := by fun_prop
  exact (hweight.mul continuous_const).mul hjet

theorem norm_weightedSemiclassicalJet_le (T : Plane → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (κ : ℝ) (u : Wavefunction) (n : ℕ) (v : Fin n → Plane)
    (hv : ∀ i, ‖v i‖ ≤ 1) (x : Plane) :
    ‖weightedSemiclassicalJet T h κ u n v x‖ ≤
      Real.exp (κ / h * T x) * h ^ n * ‖iteratedFDeriv ℝ n u x‖ := by
  have heval := (iteratedFDeriv ℝ n u x).le_opNorm_mul_prod_of_le hv
  simp only [weightedSemiclassicalJet, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hh]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa using heval

theorem weightedSemiclassicalJet_add (T : Plane → ℝ) (h κ : ℝ)
    {u w : Wavefunction} (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (v : Fin n → Plane) :
    weightedSemiclassicalJet T h κ (u + w) n v =
      weightedSemiclassicalJet T h κ u n v + weightedSemiclassicalJet T h κ w n v := by
  funext x
  simp only [weightedSemiclassicalJet, Pi.add_apply]
  rw [iteratedFDeriv_add_apply (contDiff_infty.mp hu n).contDiffAt
    (contDiff_infty.mp hw n).contDiffAt, ContinuousMultilinearMap.add_apply]
  ring

theorem weightedSemiclassicalJet_const_smul (T : Plane → ℝ) (h κ : ℝ)
    {u : Wavefunction} (hu : ContDiff ℝ ∞ u) (a : ℂ)
    (n : ℕ) (v : Fin n → Plane) :
    weightedSemiclassicalJet T h κ (a • u) n v =
      a • weightedSemiclassicalJet T h κ u n v := by
  funext x
  simp only [weightedSemiclassicalJet, Pi.smul_apply]
  rw [iteratedFDeriv_const_smul_apply (contDiff_infty.mp hu n).contDiffAt,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

end InfiniteZero
