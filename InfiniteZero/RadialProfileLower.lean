import InfiniteZero.RealRadialState
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! A lower bound near the origin, obtained by two comparisons of radial
flux derivatives. No rescaled harmonic limit or elliptic estimate is used. -/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

theorem radial_profile_quadratic_lower {f : ℝ → ℝ} {M : ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hflux : ∀ r > 0, -(M * f 0 * r) ≤ deriv (fun s => s * deriv f s) r)
    {r : ℝ} (hr : 0 ≤ r) :
    f 0 * (1 - M * r ^ 2 / 4) ≤ f r := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hfluxdiff : Differentiable ℝ (fun s => s * deriv f s) :=
    differentiable_id.mul (hf'.differentiable (by simp))
  let g : ℝ → ℝ := fun s => s * deriv f s + M * f 0 * s ^ 2 / 2
  have hg (s : ℝ) : HasDerivAt g
      (deriv (fun t => t * deriv f t) s + M * f 0 * s) s := by
    convert (hfluxdiff s).hasDerivAt.add
      ((((hasDerivAt_id s).pow 2).const_mul (M * f 0)).div_const 2) using 1
    dsimp only [g, id]
    ring
  have hgm : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (show Continuous g from (show Differentiable ℝ g from fun s =>
        (hg s).differentiableAt).continuous).continuousOn
      (fun s _ => (hg s).differentiableAt.differentiableWithinAt)
    intro s hs
    have hspos : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    rw [(hg s).deriv]
    linarith only [hflux s hspos]
  have hgpos (s : ℝ) (hs : 0 ≤ s) : 0 ≤ s * deriv f s + M * f 0 * s ^ 2 / 2 := by
    simpa only [g, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div,
      add_zero] using hgm (show (0 : ℝ) ∈ Ici 0 by simp) hs hs
  let k : ℝ → ℝ := fun s => f s + M * f 0 * s ^ 2 / 4
  have hk (s : ℝ) : HasDerivAt k (deriv f s + M * f 0 * s / 2) s := by
    convert (hf.differentiable (by simp) s).hasDerivAt.add
      ((((hasDerivAt_id s).pow 2).const_mul (M * f 0)).div_const 4) using 1
    dsimp only [k, id]
    ring
  have hkm : MonotoneOn k (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (show Continuous k from (show Differentiable ℝ k from fun s =>
        (hk s).differentiableAt).continuous).continuousOn
      (fun s _ => (hk s).differentiableAt.differentiableWithinAt)
    intro s hs
    have hspos : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    rw [(hk s).deriv]
    have hmul : 0 ≤ s * (deriv f s + M * f 0 * s / 2) := by
      nlinarith only [hgpos s hspos.le]
    exact (mul_nonneg_iff_of_pos_left hspos).mp hmul
  have h := hkm (show (0 : ℝ) ∈ Ici 0 by simp) hr hr
  dsimp only [k] at h
  nlinarith only [h]

theorem radial_profile_lower_of_flux_equation {f q : ℝ → ℝ} {M : ℝ}
    (hf : ContDiff ℝ ∞ f) (hM : 0 ≤ M)
    (hpos : ∀ r > 0, 0 ≤ f r) (hmax : ∀ r > 0, f r ≤ f 0)
    (hq : ∀ r > 0, -M ≤ q r)
    (hflux : ∀ r > 0, HasDerivAt (fun s => s * deriv f s) (r * q r * f r) r)
    {r : ℝ} (hr : 0 ≤ r) :
    f 0 * (1 - M * r ^ 2 / 4) ≤ f r := by
  apply radial_profile_quadratic_lower hf _ hr
  intro s hs
  rw [(hflux s hs).deriv]
  have h1 := mul_le_mul_of_nonneg_right (hq s hs) (hpos s hs)
  have h2 := mul_le_mul_of_nonpos_left (hmax s hs) (neg_nonpos.mpr hM)
  have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) hs.le
  nlinarith only [h3]

end InfiniteZero
