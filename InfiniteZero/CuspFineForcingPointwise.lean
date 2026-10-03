import InfiniteZero.LandauKernelExactActionUpper
import InfiniteZero.CuspWeightedActionGain
import InfiniteZero.ConstructionCuspFlat
import InfiniteZero.LogFlatIntegral

/-!
# A fine pointwise bound for the actual weighted cusp forcing

The exact exterior kernel representation, the full radial action upper bound,
and the remaining normal action gain give a log-flat improvement. The constant
and semiclassical threshold are uniform in the energy, weight strength, exterior
coefficient and wavefunction. No source estimate is an input.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero.CuspParameters

/-- The genuine perturbation times an exterior radial state satisfies a fine
pointwise bound. The coefficient of the log-flat Gaussian may be any `β₁ < β`. -/
theorem exists_cusp_fine_forcing_pointwise {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) {β₁ : ℝ}
    (_hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
      ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction,
      (∀ x, p.r₀ < ‖x‖ → φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ)) →
      ∀ x, ‖(Real.exp (κ / h * χ.weight x) : ℂ) *
        (p.atomicPerturbation x : ℂ) * φ x‖ ≤
        C * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
          Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) := by
  have ha := hp.a_pos
  have hε := hp.ε_pos
  obtain ⟨C, hC, hK⟩ := exists_uniform_landauKernel_exact_action_upper
    hp.b_pos (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hp.radius_pos (le_max_left p.R p.cuspSupportRadius)
  refine ⟨2 * p.ε * p.a * C, by positivity, ?_⟩
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin,
    eventually_logFlat_laplace_le hp.β_pos (hp.t₀_pos.trans hp.t₀_lt)
      (show (0 : ℝ) < 1 / 16 by norm_num) (sub_pos.mpr hβ₁β)]
    with h hh1 hh hlog
  have hhp : 0 < h := hh
  intro E hE κ hκ Γ hΓ φ hφ
  have hEp : 0 < E := lt_of_lt_of_le (by norm_num) hE.1
  have hcomponent (x : Plane) (q t : ℝ)
      (hq : |q| ≤ p.a * logFlat p.β p.tStar t)
      (hdata : q ≠ 0 → 0 < t ∧ p.r₀ < ‖x‖ ∧
        ‖x‖ ∈ Icc p.R p.cuspSupportRadius ∧
        κ * χ.weight x - (bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R) ≤ -t / 16) :
      ‖(Real.exp (κ / h * χ.weight x) : ℂ) * (q : ℂ) * φ x‖ ≤
        p.a * C * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
          Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) := by
    by_cases hq0 : q = 0
    · simp only [hq0, Complex.ofReal_zero, mul_zero, zero_mul, norm_zero]
      positivity
    obtain ⟨ht, hout, hrange, hgain⟩ := hdata hq0
    have hrpos : 0 < ‖x‖ := hp.radius_pos.trans_le hrange.1
    have hKpos := (landauKernel_pos hp.b_pos hhp hEp hrpos).le
    have hKbound := hK E hE ‖x‖
      ⟨hrange.1, hrange.2.trans (le_max_right _ _)⟩ h hhp hh1.le
    have hlf : 0 ≤ logFlat p.β p.tStar t := by
      rw [logFlat_of_pos p.β p.tStar ht]
      exact (Real.exp_pos _).le
    have hexp : Real.exp (κ / h * χ.weight x) *
        logFlat p.β p.tStar t * Real.exp (-bridgeAction p.b E ‖x‖ / h) ≤
        Real.exp (-bridgeAction p.b E p.R / h) *
          Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) := by
      rw [logFlat_of_pos p.β p.tStar ht, ← Real.exp_add, ← Real.exp_add]
      have hgainh := div_le_div_of_nonneg_right hgain hhp.le
      have hexponent :
          κ / h * χ.weight x + -p.β * (Real.log (p.tStar / t)) ^ 2 +
            -bridgeAction p.b E ‖x‖ / h ≤
          -bridgeAction p.b E p.R / h +
            (-p.β * (Real.log (p.tStar / t)) ^ 2 - (1 / 16 : ℝ) * t / h) := by
        convert add_le_add_right hgainh
          (-bridgeAction p.b E p.R / h - p.β * (Real.log (p.tStar / t)) ^ 2)
          using 1 <;> ring
      calc
        _ ≤ Real.exp (-bridgeAction p.b E p.R / h +
            (-p.β * (Real.log (p.tStar / t)) ^ 2 - (1 / 16 : ℝ) * t / h)) :=
          Real.exp_le_exp.mpr hexponent
        _ = Real.exp (-bridgeAction p.b E p.R / h) *
            Real.exp (-p.β * (Real.log (p.tStar / t)) ^ 2 - (1 / 16 : ℝ) * t / h) :=
          Real.exp_add _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by simpa only [sub_sub_cancel] using hlog (1 / 16) le_rfl t ht)
          (Real.exp_pos _).le
    rw [hφ x hout]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg hΓ, abs_of_nonneg hKpos]
    calc
      _ ≤ Real.exp (κ / h * χ.weight x) * (p.a * logFlat p.β p.tStar t) *
          (Γ * (C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E ‖x‖ / h))) := by
        gcongr
      _ = (p.a * C * Γ * (h ^ 2)⁻¹) *
          (Real.exp (κ / h * χ.weight x) * logFlat p.β p.tStar t *
            Real.exp (-bridgeAction p.b E ‖x‖ / h)) := by ring
      _ ≤ (p.a * C * Γ * (h ^ 2)⁻¹) *
          (Real.exp (-bridgeAction p.b E p.R / h) *
            Real.exp (-β₁ * (Real.log (1 / h)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  intro x
  have hplus := hcomponent x (p.cuspPlus x) (p.normalCoordinate x)
    (abs_cuspPlus_le_logFlat hp x) (fun hx => by
      obtain ⟨ht, hout, hrange, _, hgain⟩ :=
        χ.cuspPlus_support_weighted_action_bounds hp hE hκ hx
      exact ⟨ht.1, hout, hrange, hgain⟩)
  have hminus := hcomponent x (p.cuspMinus x) (p.normalCoordinate (reflection x))
    (abs_cuspPlus_le_logFlat hp (reflection x)) (fun hx => by
      obtain ⟨ht, hout, hrange, _, hgain⟩ :=
        χ.cuspMinus_support_weighted_action_bounds hp hE hκ hx
      exact ⟨ht.1, hout, hrange, hgain⟩)
  have hsplit : (Real.exp (κ / h * χ.weight x) : ℂ) *
      (p.atomicPerturbation x : ℂ) * φ x = (p.ε : ℂ) *
        ((Real.exp (κ / h * χ.weight x) : ℂ) * (p.cuspPlus x : ℂ) * φ x +
          (Real.exp (κ / h * χ.weight x) : ℂ) * (p.cuspMinus x : ℂ) * φ x) := by
    simp only [atomicPerturbation, Pi.sub_apply, potential, add_sub_cancel_left,
      Complex.ofReal_mul, Complex.ofReal_add]
    ring
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.ε_pos]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) hp.ε_pos.le).trans
  have hhbound := mul_le_mul_of_nonneg_left (add_le_add hplus hminus) hp.ε_pos.le
  convert hhbound using 1
  ring

end InfiniteZero.CuspParameters
