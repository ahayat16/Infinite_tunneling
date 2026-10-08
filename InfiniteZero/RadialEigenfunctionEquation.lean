import InfiniteZero.RealRadialState
import InfiniteZero.MagneticRadialReduction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The complete radial equation of a genuine smooth magnetic eigenfunction,
including the potential term. This equation is also valid inside the core. -/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

theorem IsEigenfunction.radial_profile_equation
    {b coupling E : ℝ} {V : Potential} {φ : Wavefunction}
    (hφ : IsEigenfunction b coupling V E φ) (hpos : IsPositiveRadial φ)
    {r : ℝ} (hr : 0 < r) :
    deriv (deriv (realRadialProfile φ)) r + r⁻¹ * deriv (realRadialProfile φ) r =
      (b ^ 2 * coupling ^ 2 / 4 * r ^ 2 + coupling ^ 2 * V (r • coordinateVector 0) - E) *
        realRadialProfile φ r := by
  let f := realRadialProfile φ
  have hf : ContDiff ℝ ∞ f := realRadialProfile_contDiff hφ.1
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hder (s : ℝ) : HasDerivAt f (deriv f s) s :=
    (hf.differentiable (by simp) s).hasDerivAt
  have hnorm : ‖r • coordinateVector 0‖ = r := norm_radial_axis hr.le
  have hx : r • coordinateVector 0 ≠ 0 := by
    apply norm_pos_iff.mp
    rwa [hnorm]
  have hsecond := (hf'.differentiable (by simp) r).hasDerivAt
  have hformula := magneticHamiltonian_radial (fun s _ => hder s) hx
    (by simpa only [hnorm] using hsecond) b coupling V
  have heigen := hφ.2.2 (r • coordinateVector 0)
  have hradial : φ = fun x : Plane => (f ‖x‖ : ℂ) := hpos.eq_radial_function
  rw [hradial, hformula] at heigen
  simp only [hnorm] at heigen
  have hreal := congrArg Complex.re heigen
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero] at hreal
  change deriv (deriv f) r + r⁻¹ * deriv f r = _
  nlinarith only [hreal]

theorem IsEigenfunction.hasDerivAt_radial_flux
    {b coupling E : ℝ} {V : Potential} {φ : Wavefunction}
    (hφ : IsEigenfunction b coupling V E φ) (hpos : IsPositiveRadial φ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => s * deriv (realRadialProfile φ) s)
      (r * (b ^ 2 * coupling ^ 2 / 4 * r ^ 2 +
        coupling ^ 2 * V (r • coordinateVector 0) - E) * realRadialProfile φ r) r := by
  have hf := realRadialProfile_contDiff hφ.1
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hd := (hasDerivAt_id r).mul ((hf'.differentiable (by simp) r).hasDerivAt)
  have heq := hφ.radial_profile_equation hpos hr
  have hscale := congrArg (fun z : ℝ => r * z) heq
  have hcancel : r * (r⁻¹ * deriv (realRadialProfile φ) r) =
      deriv (realRadialProfile φ) r := by field_simp
  dsimp only at hscale
  rw [mul_add, hcancel] at hscale
  convert hd using 1
  dsimp only [id]
  nlinarith only [hscale]

end InfiniteZero
