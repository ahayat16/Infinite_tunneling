import InfiniteZero.ComplexLandauDerivativeBounds
import InfiniteZero.RadialCompositionJetBounds

/-!
# Exact-action spatial derivative bounds for the radial Landau kernel

On a fixed positive annulus, a common bound for all radial derivatives
through order `n` passes to the spatial derivative of order `n`. The full
action at the evaluation radius is retained, with polynomial cost `h⁻⁽ⁿ⁺²⁾`.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

/-- The real proper-time kernel is smooth on positive radii, by restriction
of its holomorphic extension. No smoothness at the origin is asserted. -/
theorem contDiffOn_landauKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) :
    ContDiffOn ℝ ∞ (landauKernel b h E) (Ioi 0) := by
  intro r hr
  have ha : AnalyticAt ℂ (complexLandauKernel b h E) (r : ℂ) :=
    analyticOnNhd_complexLandauKernel hb hh hE _ (by
      simpa only [complexLandauRadiusDomain, mem_setOf_eq, ← Complex.ofReal_pow,
        Complex.ofReal_re] using sq_pos_of_pos hr)
  have hc : ContDiffAt ℂ ∞ (complexLandauKernel b h E) (r : ℂ) := ha.contDiffAt
  simpa only [complexLandauKernel_ofReal, Complex.ofReal_re] using
    hc.real_of_complex.contDiffWithinAt (s := Ioi 0)

/-- Every radial derivative up to the prescribed order has the same
majorant. The constant may depend on the maximum order, while energy,
radius, semiclassical parameter and lower derivative order remain uniform. -/
theorem exists_uniform_landauKernel_radialJet_bound
    {b Emin Emax rMin rMax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin)
    (hEmax : Emin ≤ Emax) (hMin : 0 < rMin) (hMax : rMin ≤ rMax) (n : ℕ) :
    ∃ C > 0, ∃ h₀ > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rMin rMax,
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ i : ℕ, i ≤ n →
        ‖iteratedDeriv i (landauKernel b h E) r‖ ≤
          C * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E r / h) := by
  obtain ⟨C, hC, h₀, hh₀, hbound⟩ :=
    exists_uniform_landauKernel_iteratedDeriv_bound hb hEmin hEmax hMin hMax
  have hn : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  refine ⟨(n.factorial : ℝ) * C, by positivity,
    min h₀ 1, lt_min hh₀ zero_lt_one, ?_⟩
  intro E hE r hr h hh hsmall i hi
  have hfact : (i.factorial : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.factorial_le hi
  have hpow : h ^ (n + 2) ≤ h ^ (i + 2) :=
    pow_le_pow_of_le_one hh.le (hsmall.trans (min_le_right _ _))
      (Nat.add_le_add_right hi 2)
  have hinv : (h ^ (i + 2))⁻¹ ≤ (h ^ (n + 2))⁻¹ :=
    (inv_le_inv₀ (pow_pos hh _) (pow_pos hh _)).mpr hpow
  apply (hbound i E hE r hr h hh (hsmall.trans (min_le_left _ _))).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right hfact hC.le) hinv
      (inv_nonneg.mpr (pow_nonneg hh.le _)) (by positivity)) (Real.exp_pos _).le

/-- Spatial derivatives of the actual radial kernel obey the same full
action bound on a positive annulus. Constants depend on the fixed order and
the parameter rectangle, not on energy, point or semiclassical parameter. -/
theorem exists_uniform_landauKernel_spatialDerivative_bound
    {b Emin Emax rMin rMax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin)
    (hEmax : Emin ≤ Emax) (hMin : 0 < rMin) (hMax : rMin ≤ rMax) (n : ℕ) :
    ∃ C > 0, ∃ h₀ > 0, ∀ E ∈ Icc Emin Emax,
      ∀ x : Plane, ‖x‖ ∈ Icc rMin rMax → ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ‖iteratedFDeriv ℝ n (fun y : Plane => landauKernel b h E ‖y‖) x‖ ≤
          C * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E ‖x‖ / h) := by
  obtain ⟨Cr, hCr, h₀, hh₀, hradial⟩ :=
    exists_uniform_landauKernel_radialJet_bound hb hEmin hEmax hMin hMax n
  obtain ⟨Cs, hCs, hcomposition⟩ :=
    exists_radial_composition_jet_bound (rMax := rMax) hMin n
  refine ⟨Cs * Cr, by positivity, h₀, hh₀, ?_⟩
  intro E hE x hx h hh hsmall
  have hjet := hradial E hE ‖x‖ hx h hh hsmall
  have hbound := hcomposition (landauKernel b h E)
    (contDiffOn_landauKernel hb hh (hEmin.trans_le hE.1)) x hx
    (Cr * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E ‖x‖ / h))
    (by positivity) hjet
  simpa only [mul_assoc] using hbound

/-- A common spatial majorant for every order up to `n`, using one radial
jet bound and a finite sum of composition constants. In particular there
is no derivative-order-dependent semiclassical threshold in the conclusion. -/
theorem exists_uniform_landauKernel_spatialJet_bound
    {b Emin Emax rMin rMax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin)
    (hEmax : Emin ≤ Emax) (hMin : 0 < rMin) (hMax : rMin ≤ rMax) (n : ℕ) :
    ∃ C > 0, ∃ h₀ > 0, ∀ E ∈ Icc Emin Emax,
      ∀ x : Plane, ‖x‖ ∈ Icc rMin rMax → ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ∀ j : ℕ, j ≤ n →
          ‖iteratedFDeriv ℝ j (fun y : Plane => landauKernel b h E ‖y‖) x‖ ≤
            C * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E ‖x‖ / h) := by
  obtain ⟨Cr, hCr, h₀, hh₀, hradial⟩ :=
    exists_uniform_landauKernel_radialJet_bound hb hEmin hEmax hMin hMax n
  choose Cs hCs hcomposition using fun j : ℕ =>
    exists_radial_composition_jet_bound (rMax := rMax) hMin j
  let Csum := 1 + ∑ j ∈ Finset.range (n + 1), Cs j
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), Cs j :=
    Finset.sum_nonneg (fun j _ => (hCs j).le)
  have hCsum : 0 < Csum := by dsimp [Csum]; linarith
  refine ⟨Csum * Cr, by positivity, h₀, hh₀, ?_⟩
  intro E hE x hx h hh hsmall j hj
  have hjet (i : ℕ) (hi : i ≤ j) :=
    hradial E hE ‖x‖ hx h hh hsmall i (hi.trans hj)
  have hCsj : Cs j ≤ Csum := by
    have hle : Cs j ≤ ∑ i ∈ Finset.range (n + 1), Cs i :=
      Finset.single_le_sum (fun i _ => (hCs i).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    dsimp [Csum]
    linarith
  calc
    _ ≤ Cs j * (Cr * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E ‖x‖ / h)) :=
      hcomposition j (landauKernel b h E)
        (contDiffOn_landauKernel hb hh (hEmin.trans_le hE.1)) x hx _ (by positivity) hjet
    _ ≤ Csum * (Cr * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E ‖x‖ / h)) :=
      mul_le_mul_of_nonneg_right hCsj (by positivity)
    _ = _ := by ring

end InfiniteZero
