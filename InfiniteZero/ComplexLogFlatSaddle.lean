import InfiniteZero.ComplexLambertAsymptotics
import InfiniteZero.ComplexLogFlatPhase

/-!
# The actual complex saddle for the log-flat normal integral

This module instantiates the proved large Lambert root at the actual
coefficient `c * tStar / h`. No existence of a critical point is assumed.
The order of parameters is fixed `β,k,tStar,c`, then `h → 0+`.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

def logFlatLambertDisplacement (β k tStar : ℝ) (c : ℂ) : ℂ :=
  Complex.log (c * (tStar : ℂ) / (2 * (β : ℂ))) +
    (((k + 1) / (2 * β) : ℝ) : ℂ)

def logFlatSaddleRoot (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℂ :=
  largeLambertRoot ((Real.log (1 / h) : ℂ) + logFlatLambertDisplacement β k tStar c)

theorem eventually_logFlatSaddleRoot_log_eq (β k tStar : ℝ) (c : ℂ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      logFlatSaddleRoot β k tStar c h + Complex.log (logFlatSaddleRoot β k tStar c h) =
        (Real.log (1 / h) : ℂ) + logFlatLambertDisplacement β k tStar c := by
  have hlog : Tendsto (fun h : ℝ => Real.log (1 / h)) (𝓝[>] 0) atTop := by
    simpa only [one_div] using Real.tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop)
  filter_upwards [hlog.eventually (eventually_largeLambertRoot_real_add_estimates
    ‖logFlatLambertDisplacement β k tStar c‖)] with h hs
  exact (hs (logFlatLambertDisplacement β k tStar c) le_rfl).2.2.1

theorem exp_logFlatLambertInput {β k tStar h : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : tStar ≠ 0) (hc : c ≠ 0) (hh : 0 < h) :
    Complex.exp ((Real.log (1 / h) : ℂ) + logFlatLambertDisplacement β k tStar c) =
      (c * (tStar : ℂ) / (h : ℂ)) *
        Complex.exp (((k + 1) / (2 * β) : ℝ) : ℂ) / (2 * (β : ℂ)) := by
  have hz : c * (tStar : ℂ) / (2 * (β : ℂ)) ≠ 0 :=
    div_ne_zero (mul_ne_zero hc (Complex.ofReal_ne_zero.mpr ht))
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hβ))
  simp only [logFlatLambertDisplacement, Complex.exp_add, Complex.exp_log hz,
    ← Complex.ofReal_exp, Real.exp_log (one_div_pos.mpr hh)]
  push_cast
  ring

theorem eventually_logFlatSaddleRoot_equation {β k tStar : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : tStar ≠ 0) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      2 ≤ (logFlatSaddleRoot β k tStar c h).re ∧
      Real.log (1 / h) / 2 ≤ (logFlatSaddleRoot β k tStar c h).re ∧
      logFlatSaddleRoot β k tStar c h * Complex.exp (logFlatSaddleRoot β k tStar c h) =
        (c * (tStar : ℂ) / (h : ℂ)) *
          Complex.exp (((k + 1) / (2 * β) : ℝ) : ℂ) / (2 * (β : ℂ)) ∧
      |(logFlatSaddleRoot β k tStar c h).im| ≤
        ‖logFlatLambertDisplacement β k tStar c‖ + Real.pi := by
  have hlog : Tendsto (fun h : ℝ => Real.log (1 / h)) (𝓝[>] 0) atTop := by
    simpa only [one_div] using Real.tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop)
  have he := hlog.eventually
    (eventually_largeLambertRoot_real_add_estimates ‖logFlatLambertDisplacement β k tStar c‖)
  filter_upwards [he, self_mem_nhdsWithin] with h he hh
  have hs := he (logFlatLambertDisplacement β k tStar c) le_rfl
  refine ⟨hs.1, hs.2.1, ?_, hs.2.2.2.2.2.1⟩
  change largeLambertRoot _ * Complex.exp (largeLambertRoot _) = _
  rw [hs.2.2.2.1, exp_logFlatLambertInput hβ ht hc hh]

theorem eventually_logFlatSaddleRoot_critical {β k tStar : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : tStar ≠ 0) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (c * (tStar : ℂ) / (h : ℂ)) *
        Complex.exp (-logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)) =
          2 * (β : ℂ) * logFlatSaddleRoot β k tStar c h ∧
      deriv (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ)))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)) = 0 := by
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ ht hc] with h hs
  have he := logFlat_critical_exponential hβ hs.2.2.1
  exact ⟨he, logFlatComplexCritical_deriv_eq_zero hβ he⟩

theorem eventually_logFlatSaddleRoot_location {β k tStar : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : tStar ≠ 0) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (tStar : ℂ) *
        Complex.exp (-logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)) =
          (2 * (β : ℂ) * (h : ℂ) / c) * logFlatSaddleRoot β k tStar c h := by
  filter_upwards [eventually_logFlatSaddleRoot_critical (k := k) hβ ht hc, self_mem_nhdsWithin]
    with h hs hh
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hh)
  have he := hs.1
  field_simp [hh'] at he
  field_simp [hc]
  linear_combination he

theorem tendsto_re_logFlatSaddleRoot {β k tStar : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : tStar ≠ 0) (hc : c ≠ 0) :
    Tendsto (fun h : ℝ => (logFlatSaddleRoot β k tStar c h).re) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun h : ℝ => Real.log (1 / h)) (𝓝[>] 0) atTop := by
    simpa only [one_div] using Real.tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop)
  apply tendsto_atTop_mono' _ _ (hlog.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ ht hc] with h hs
  exact hs.2.1

/-- The actual critical value and Hessian, with no saddle equation as an input. -/
theorem eventually_logFlatSaddleRoot_value_hessian {β k tStar : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : tStar ≠ 0) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)) =
          (β : ℂ) * ((logFlatSaddleRoot β k tStar c h) ^ 2 +
            2 * logFlatSaddleRoot β k tStar c h) -
            (((k + 1) ^ 2 / (4 * β) : ℝ) : ℂ) ∧
      deriv (deriv (logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))))
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)) =
          2 * (β : ℂ) * (1 + logFlatSaddleRoot β k tStar c h) := by
  filter_upwards [eventually_logFlatSaddleRoot_critical (k := k) hβ ht hc] with h hs
  exact ⟨logFlatComplexCritical_value hβ hs.1, logFlatComplexCritical_hessian β k hs.1⟩

theorem eventually_norm_logFlatSaddleRoot_le (β k tStar : ℝ) (c : ℂ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖logFlatSaddleRoot β k tStar c h‖ ≤ 2 * Real.log (1 / h) := by
  let d := logFlatLambertDisplacement β k tStar c
  have hlog : Tendsto (fun h : ℝ => Real.log (1 / h)) (𝓝[>] 0) atTop := by
    simpa only [one_div] using Real.tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop)
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16)
  have hlarge : ∀ᶠ ℓ : ℝ in atTop,
      ‖largeLambertRoot ((ℓ : ℂ) + d)‖ ≤ 2 * ℓ := by
    filter_upwards [eventually_largeLambertRoot_real_add_estimates ‖d‖,
      eventually_ge_atTop (4 * ‖d‖), eventually_ge_atTop (1 : ℝ), hsmall]
      with ℓ hroot hd hℓ hsmall
    have hℓpos : 0 ≤ ℓ := by linarith
    have hlogpos : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
    simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hℓpos,
      abs_of_nonneg hlogpos] at hsmall
    have hroot' := (hroot d le_rfl).2.2.2.2.2.2
    have htri := norm_add_le (largeLambertRoot ((ℓ : ℂ) + d) - ((ℓ : ℂ) + d))
      ((ℓ : ℂ) + d)
    rw [sub_add_cancel] at htri
    have hL := norm_add_le (ℓ : ℂ) d
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hℓpos] at hL
    linarith
  exact hlog.eventually hlarge

theorem eventually_logFlatSaddle_location_bound {β k tStar : ℝ} {c : ℂ}
    (hβ : β ≠ 0) (ht : tStar ≠ 0) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖(tStar : ℂ) *
        Complex.exp (-logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))‖ ≤
          (4 * |β| / ‖c‖) * h * Real.log (1 / h) := by
  filter_upwards [eventually_logFlatSaddleRoot_location (k := k) hβ ht hc,
    eventually_norm_logFlatSaddleRoot_le β k tStar c, self_mem_nhdsWithin]
      with h hloc hbound hh
  rw [hloc, norm_mul, norm_div, norm_mul, norm_mul]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < h from hh)]
  calc
    2 * |β| * h / ‖c‖ * ‖logFlatSaddleRoot β k tStar c h‖ ≤
        2 * |β| * h / ‖c‖ * (2 * Real.log (1 / h)) := by
      apply mul_le_mul_of_nonneg_left hbound
      have hhpos : 0 < h := hh
      positivity
    _ = (4 * |β| / ‖c‖) * h * Real.log (1 / h) := by ring

end InfiniteZero
