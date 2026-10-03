import InfiniteZero.LandauLaplaceTails
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Radial variation of the critical proper time

The explicit derivative gives a uniform Lipschitz constant depending only on a
positive lower energy bound. Consequently a small change of radius moves the
center of the proper-time tails by a controlled amount.
-/

noncomputable section
open Set

namespace InfiniteZero

private theorem bridgeTime_sqrt_rescale (b r : ℝ) {E : ℝ} (hE : 0 < E) :
    Real.sqrt (1 + (b * r / (2 * Real.sqrt E)) ^ 2) =
      Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) / (2 * Real.sqrt E) := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hs2 := Real.sq_sqrt hE.le
  have hA := Real.sq_sqrt (show 0 ≤ b ^ 2 * r ^ 2 + 4 * E by positivity)
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  field_simp
  nlinarith

/-- The radial derivative is valid on the entire real line. -/
theorem hasDerivAt_bridgeTime_radial {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E)
    (r : ℝ) :
    HasDerivAt (bridgeTime b E) (1 / Real.sqrt (b ^ 2 * r ^ 2 + 4 * E)) r := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hA : 0 < Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) := Real.sqrt_pos.2 (by positivity)
  have hd := ((((hasDerivAt_id r).const_mul b).div_const
    (2 * Real.sqrt E)).arsinh).div_const b
  convert hd using 1
  simp only [id, mul_one, smul_eq_mul]
  rw [bridgeTime_sqrt_rescale b r hE]
  field_simp

theorem deriv_bridgeTime_radial {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    deriv (bridgeTime b E) r = 1 / Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) :=
  (hasDerivAt_bridgeTime_radial hb hE r).deriv

theorem norm_deriv_bridgeTime_radial_le {b E Emin : ℝ}
    (hb : b ≠ 0) (hEmin : 0 < Emin) (hE : Emin ≤ E) (r : ℝ) :
    ‖deriv (bridgeTime b E) r‖ ≤ 1 / (2 * Real.sqrt Emin) := by
  have hEpos : 0 < E := lt_of_lt_of_le hEmin hE
  have hrad : 0 < b ^ 2 * r ^ 2 + 4 * E := by positivity
  have hroot : 2 * Real.sqrt Emin ≤ Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) := by
    have hminSq := Real.sq_sqrt hEmin.le
    have hradSq := Real.sq_sqrt hrad.le
    have hmin0 := Real.sqrt_nonneg Emin
    have hrad0 := Real.sqrt_nonneg (b ^ 2 * r ^ 2 + 4 * E)
    nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg r)]
  rw [deriv_bridgeTime_radial hb hEpos, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / Real.sqrt (b ^ 2 * r ^ 2 + 4 * E))]
  exact one_div_le_one_div_of_le (by positivity) hroot

/-- Uniform radial Lipschitz estimate without an upper bound on the energy or radii. -/
theorem abs_bridgeTime_sub_le {b E Emin : ℝ}
    (hb : b ≠ 0) (hEmin : 0 < Emin) (hE : Emin ≤ E) (r s : ℝ) :
    |bridgeTime b E r - bridgeTime b E s| ≤ |r - s| / (2 * Real.sqrt Emin) := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := bridgeTime b E)
    (fun x _ => (hasDerivAt_bridgeTime_radial hb (lt_of_lt_of_le hEmin hE) x).differentiableAt)
    (fun x _ => norm_deriv_bridgeTime_radial_le hb hEmin hE x)
    convex_univ (mem_univ s) (mem_univ r)
  simpa only [Real.norm_eq_abs, one_div, div_eq_mul_inv, mul_comm, one_mul] using h

/-- Changing the radius by this amount preserves the tail outside half the original window. -/
theorem landauTailSet_subset_of_radius_sub_le {b E Emin r ρ ε : ℝ}
    (hb : b ≠ 0) (hEmin : 0 < Emin) (hE : Emin ≤ E)
    (hclose : |ρ - r| / (2 * Real.sqrt Emin) ≤ ε / 2) :
    landauTailSet b E r ε ⊆ landauTailSet b E ρ (ε / 2) := by
  intro τ hτ
  refine ⟨hτ.1, ?_⟩
  have hcenter := (abs_bridgeTime_sub_le hb hEmin hE ρ r).trans hclose
  have htriangle := abs_sub_le τ (bridgeTime b E ρ) (bridgeTime b E r)
  have hfar := hτ.2
  linarith

end InfiniteZero
