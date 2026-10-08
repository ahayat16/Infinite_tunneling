import InfiniteZero.ExteriorRadialJetBounds
import InfiniteZero.RadialCoreEnergyBounds
import InfiniteZero.RadialCoreExteriorState
import InfiniteZero.CuspWeightApproximation
import InfiniteZero.RadialCoreNormalizationUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential decay of weighted jets of the true radial core state

On a fixed annulus containing the cusp supports, the action gained from
radius `2 * r₀` absorbs the exterior normalization coefficient, a small
fixed weight, and every fixed polynomial derivative loss. The weight is
applied after differentiation. All constants precede the coupling and the
choice of normalized positive radial ground state.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

/-- A uniform positive action margin between the normalization radius and
the inner radius of the fixed cusp neighborhood. -/
theorem radialCore_annulus_action_gap {p : CuspParameters} (hp : p.BasicConditions)
    {E r : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1) (hr : p.R / 2 ≤ r) :
    (p.R / 2 - 2 * p.r₀) / 2 ≤
      bridgeAction p.b E r - bridgeAction p.b E (2 * p.r₀) := by
  have hEpos : 0 < E := by linarith [hE.1]
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt E := by
    nlinarith [Real.sq_sqrt hEpos.le, Real.sqrt_nonneg E, hE.1]
  have hr0 : 2 * p.r₀ ≤ r := by linarith [hp.radius_large, hp.r₀_pos]
  have hgain := bridgeAction_sub_ge hp.b_pos.ne' hEpos hr0
  have hmul := mul_le_mul_of_nonneg_right hsqrt (sub_nonneg.mpr hr0)
  linarith

private theorem eventually_pow_le_small_exp {d : ℝ} (hd : 0 < d) (n : ℕ) :
    ∀ᶠ coupling : ℝ in atTop, coupling ^ n ≤ Real.exp (d * coupling) := by
  filter_upwards [(isLittleO_pow_exp_pos_mul_atTop n hd).bound zero_lt_one,
    eventually_ge_atTop (0 : ℝ)] with coupling hb hc
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc n),
    abs_of_pos (Real.exp_pos _), one_mul] using hb

/-- Numerical cancellation of the normalization factor against the kernel
prefactor. The remaining action margin absorbs the fixed exponential weight.
This lemma does not assume an estimate on the weighted jet itself. -/
theorem weighted_jet_le_of_tail_bounds
    {coupling δ κ T Γ CJ CG J₀ Jr A : ℝ} (n j : ℕ)
    (hc : 0 < coupling) (hc1 : 1 ≤ coupling)
    (hCJ : 0 ≤ CJ) (hCG : 0 ≤ CG) (hA0 : 0 ≤ A)
    (hweight : κ * T ≤ δ / 4) (hgap : δ ≤ Jr - J₀)
    (hA : A ≤ CJ * Γ * coupling ^ (n + 2) * Real.exp (-coupling * Jr))
    (hΓ : Γ ≤ CG * (coupling⁻¹) ^ 2 * Real.exp (coupling * (J₀ + δ / 4))) :
    Real.exp (κ * coupling * T) * (coupling⁻¹) ^ j * A ≤
      CJ * CG * coupling ^ n * Real.exp (-(δ / 2) * coupling) := by
  have hinv : coupling⁻¹ ≤ 1 := (inv_le_one₀ hc).mpr hc1
  have hpow : (coupling⁻¹) ^ j ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hc.le) hinv
  have hcancel : (coupling⁻¹) ^ 2 * coupling ^ (n + 2) = coupling ^ n := by
    rw [pow_add]
    field_simp
  calc
    _ ≤ Real.exp (κ * coupling * T) * 1 * A := by gcongr
    _ = Real.exp (κ * coupling * T) * A := by ring
    _ ≤ Real.exp (κ * coupling * T) *
        (CJ * Γ * coupling ^ (n + 2) * Real.exp (-coupling * Jr)) := by gcongr
    _ ≤ Real.exp (κ * coupling * T) *
        (CJ * (CG * (coupling⁻¹) ^ 2 * Real.exp (coupling * (J₀ + δ / 4))) *
          coupling ^ (n + 2) * Real.exp (-coupling * Jr)) := by gcongr
    _ = CJ * CG * ((coupling⁻¹) ^ 2 * coupling ^ (n + 2)) *
        Real.exp (κ * coupling * T + coupling * (J₀ + δ / 4) + (-coupling * Jr)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = CJ * CG * coupling ^ n *
        Real.exp (coupling * (κ * T + J₀ + δ / 4 - Jr)) := by
      rw [hcancel]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hm := mul_le_mul_of_nonneg_left
        (show κ * T + J₀ + δ / 4 - Jr ≤ -(δ / 2) by linarith) hc.le
      nlinarith

/-- On any fixed outer annulus, all the weighted semiclassical jets through
order `n` of the genuine positive radial core ground state decay exponentially.
The normalization coefficient has been eliminated using the same state's
tail at its actual energy. The rate and constants precede the coupling,
state, weight strength, point and derivative order. -/
theorem exists_radialCore_weighted_jet_decay_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (χ : CuspWeightCutoffs p) {rMax : ℝ} (hMax : p.R / 2 ≤ rMax) (n : ℕ) :
    ∃ κ₀ > 0, κ₀ ≤ (1 / 16 : ℝ) ∧ ∃ C > 0, ∃ d > 0, ∃ N > 0,
      ∀ coupling : ℝ, N ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ →
      IsPositiveRadial φ → ∀ κ ∈ Icc (0 : ℝ) κ₀,
      ∀ x : Plane, ‖x‖ ∈ Icc (p.R / 2) rMax → ∀ j : ℕ, j ≤ n →
        Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
          ‖iteratedFDeriv ℝ j φ x‖ ≤ C * Real.exp (-d * coupling) := by
  let δ := (p.R / 2 - 2 * p.r₀) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [hp.radius_large, hp.r₀_pos]
  have hd : 0 < δ / 4 := by positivity
  obtain ⟨B, hB⟩ := χ.weight_hasCompactSupport.exists_bound_of_continuous
    χ.weight_lipschitz.choose_spec.continuous
  let M := |B| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hweightBound (x : Plane) : χ.weight x ≤ M := by
    have hb := hB x
    have hχ := χ.weight_nonneg x
    simp only [Real.norm_eq_abs, abs_of_nonneg hχ] at hb
    dsimp [M]
    linarith [le_abs_self B]
  let κ₀ := min (1 / 16 : ℝ) (δ / (4 * (M + 1)))
  have hκ₀ : 0 < κ₀ := lt_min (by norm_num) (by positivity)
  have hκ₀le : κ₀ ≤ (1 / 16 : ℝ) := min_le_left _ _
  have hweighted (κ : ℝ) (hκ : κ ∈ Icc 0 κ₀) (x : Plane) :
      κ * χ.weight x ≤ δ / 4 := by
    calc
      _ ≤ κ * M := mul_le_mul_of_nonneg_left (hweightBound x) hκ.1
      _ ≤ κ * (M + 1) := by nlinarith [hκ.1]
      _ ≤ (δ / (4 * (M + 1))) * (M + 1) :=
        mul_le_mul_of_nonneg_right (hκ.2.trans (min_le_right _ _)) (by positivity)
      _ = δ / 4 := by field_simp
  obtain ⟨CG, hCG, NG, _hNG, hGamma⟩ :=
    exists_radialCore_coefficient_exp_upper_of_radialData hp hRad hAcore hd
  obtain ⟨CJ, hCJ, h₀, hh₀, hjets⟩ :=
    exists_uniform_exterior_landau_jet_bound hp.b_pos
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      hp.r₀_pos.le (show p.r₀ < p.R / 2 by linarith [hp.radius_large, hp.r₀_pos]) hMax n
  obtain ⟨NE, _hNE, henergy⟩ :=
    exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  obtain ⟨NP, hpoly⟩ := eventually_atTop.mp (eventually_pow_le_small_exp hd n)
  let N := max 1 (max NG (max NE (max h₀⁻¹ NP)))
  have hN : 0 < N := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨κ₀, hκ₀, hκ₀le, CJ * CG, by positivity, δ / 4, hd, N, hN, ?_⟩
  intro coupling hc φ hφ hpos κ hκ x hx j hj
  have hc1 : 1 ≤ coupling := (le_max_left _ _).trans hc
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  have hcG : NG ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcE : NE ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hcJ : h₀⁻¹ ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hcP : NP ≤ coupling := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hE := henergy coupling hcE
  obtain ⟨Γ, hΓ, htail⟩ := hφ.exists_pos_radialCore_kernel
    hp.b_pos hp.r₀_pos hcpos hpos (by linarith only [hE.1])
  have hG := hGamma coupling hcG φ hφ hpos Γ htail
  have hJ := hjets _ hE coupling⁻¹ (inv_pos.mpr hcpos)
    ((inv_le_comm₀ hcpos hh₀).mpr hcJ) Γ hΓ.le φ htail x hx j hj
  have hJ' : ‖iteratedFDeriv ℝ j φ x‖ ≤ CJ * Γ * coupling ^ (n + 2) *
      Real.exp (-coupling * bridgeAction p.b
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖) := by
    simpa only [inv_pow, inv_inv, div_eq_mul_inv, neg_mul, mul_neg, mul_comm, mul_left_comm,
      mul_assoc] using hJ
  have hbound := weighted_jet_le_of_tail_bounds n j hcpos hc1 hCJ.le hCG.le
    (norm_nonneg _) (hweighted κ hκ x) (radialCore_annulus_action_gap hp hE hx.1) hJ' hG
  calc
    _ ≤ CJ * CG * coupling ^ n * Real.exp (-(δ / 2) * coupling) := hbound
    _ ≤ CJ * CG * Real.exp (δ / 4 * coupling) *
        Real.exp (-(δ / 2) * coupling) := by gcongr; exact hpoly coupling hcP
    _ = CJ * CG * Real.exp (-(δ / 4) * coupling) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end InfiniteZero.CuspParameters
