import InfiniteZero.MagneticModel
import Mathlib.Analysis.Complex.RealDeriv

/-! A real radial profile taken from a smooth planar wavefunction. These
definitions fix the phase only when positivity is explicitly established;
they say nothing about the arbitrary choice `canonicalAtomicState`. -/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

def realRadialProfile (φ : Wavefunction) (r : ℝ) : ℝ :=
  (φ (r • coordinateVector 0)).re

/-- A pointwise real, radial and strictly positive wavefunction. -/
structure IsPositiveRadial (φ : Wavefunction) : Prop where
  radial : ∀ x : Plane, φ x = (realRadialProfile φ ‖x‖ : ℂ)
  positive : ∀ x : Plane, 0 < (φ x).re

theorem norm_coordinateVector (i : Fin 2) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector, PiLp.norm_single]

theorem norm_radial_axis {r : ℝ} (hr : 0 ≤ r) :
    ‖r • coordinateVector 0‖ = r := by
  simp [norm_smul, norm_coordinateVector, Real.norm_eq_abs, abs_of_nonneg hr]

theorem realRadialProfile_contDiff {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (realRadialProfile φ) := by
  exact Complex.reCLM.contDiff.comp (hφ.comp (contDiff_id.smul contDiff_const))

theorem IsPositiveRadial.profile_pos {φ : Wavefunction} (hφ : IsPositiveRadial φ)
    (r : ℝ) : 0 < realRadialProfile φ r :=
  hφ.positive (r • coordinateVector 0)

theorem IsPositiveRadial.profile_eq_re {φ : Wavefunction} (hφ : IsPositiveRadial φ)
    (x : Plane) : realRadialProfile φ ‖x‖ = (φ x).re := by
  rw [hφ.radial x]
  simp

theorem IsPositiveRadial.eq_radial_function {φ : Wavefunction} (hφ : IsPositiveRadial φ) :
    φ = fun x : Plane => (realRadialProfile φ ‖x‖ : ℂ) :=
  funext hφ.radial

end InfiniteZero
