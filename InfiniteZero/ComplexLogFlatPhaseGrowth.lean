import InfiniteZero.ComplexLogFlatNormalization
import InfiniteZero.ComplexLambertRegularity

/-!
# Continuous sublinear phase of the constructed log-flat saddle

All parameters are fixed before the coupling tends to infinity. The actual
Lambert input eventually lies in its proved open regularity domain; no
continuous branch is assumed. The positive Gaussian prefactor introduces no
additional phase.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

theorem eventually_real_add_mem_largeLambertRegularityDomain (d : ℂ) :
    ∀ᶠ ℓ : ℝ in atTop, (ℓ : ℂ) + d ∈ largeLambertRegularityDomain := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [eventually_gt_atTop (4 * ‖d‖ + 16), hsmall] with ℓ hℓ hsmall
  have hlarge : 16 < ℓ := by linarith [norm_nonneg d]
  have hpos : 0 < ℓ := by linarith
  have hlogpos : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hpos.le,
    abs_of_nonneg hlogpos] at hsmall
  refine ⟨ℓ / 2, by positivity, ?_, ?_⟩
  · have hd := Complex.abs_re_le_norm d
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [neg_le_abs d.re]
  · have hb := norm_complex_log_real_add_le hpos
      (show 2 * ‖d‖ ≤ ℓ by linarith [norm_nonneg d]) le_rfl
    rw [abs_of_nonneg hlogpos] at hb
    linarith

/-- Continuity of the constructed root as a function of the physical coupling. -/
theorem eventually_continuousAt_logFlatSaddleRoot_inv
    (β k tStar : ℝ) (c : ℂ) :
    ∀ᶠ lam : ℝ in atTop,
      ContinuousAt (fun μ : ℝ => logFlatSaddleRoot β k tStar c μ⁻¹) lam := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_real_add_mem_largeLambertRegularityDomain
      (logFlatLambertDisplacement β k tStar c)), eventually_gt_atTop (0 : ℝ)]
      with lam hdomain hlam
  obtain ⟨R, hR, hreal, hlog⟩ := hdomain
  simp only [logFlatSaddleRoot, one_div, inv_inv]
  have hin : ContinuousAt (fun μ : ℝ => (Real.log μ : ℂ) +
      logFlatLambertDisplacement β k tStar c) lam :=
    (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_log hlam.ne')).add continuousAt_const
  have hout : ContinuousAt largeLambertRoot ((Real.log lam : ℂ) +
      logFlatLambertDisplacement β k tStar c) :=
    continuousAt_largeLambertRoot hR hreal hlog
  exact hout.comp (f := fun μ : ℝ => (Real.log μ : ℂ) +
    logFlatLambertDisplacement β k tStar c) hin

/-- The value of the original phase at the constructed complex critical point. -/
def logFlatSaddleValue (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℂ :=
  logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
    (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h))

/-- A real-valued phase, with no choice of an argument modulo `2π`. -/
def logFlatSaddlePhase (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℝ :=
  -(logFlatSaddleValue β k tStar c h).im

theorem eventually_continuousAt_logFlatSaddleValue_inv
    (β k tStar : ℝ) (c : ℂ) :
    ∀ᶠ lam : ℝ in atTop,
      ContinuousAt (fun μ : ℝ => logFlatSaddleValue β k tStar c μ⁻¹) lam := by
  filter_upwards [eventually_continuousAt_logFlatSaddleRoot_inv β k tStar c,
    eventually_gt_atTop (0 : ℝ)] with lam hw hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hine : ((lam⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hne)
  have hcast : ContinuousAt (fun μ : ℝ => ((μ⁻¹ : ℝ) : ℂ)) lam :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.inv₀ hne)
  unfold logFlatSaddleValue logFlatComplexPhase logFlatComplexCritical
  fun_prop

theorem eventually_continuousAt_logFlatSaddlePhase_inv
    (β k tStar : ℝ) (c : ℂ) :
    ∀ᶠ lam : ℝ in atTop,
      ContinuousAt (fun μ : ℝ => logFlatSaddlePhase β k tStar c μ⁻¹) lam := by
  filter_upwards [eventually_continuousAt_logFlatSaddleValue_inv β k tStar c] with lam hlam
  exact (Complex.continuous_im.continuousAt.comp hlam).neg

theorem exists_continuousOn_logFlatSaddlePhase_inv (β k tStar : ℝ) (c : ℂ) :
    ∃ coupling₀ : ℝ, 0 < coupling₀ ∧
      ContinuousOn (fun μ : ℝ => logFlatSaddlePhase β k tStar c μ⁻¹) (Ici coupling₀) := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (eventually_continuousAt_logFlatSaddlePhase_inv β k tStar c)
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro coupling hcoupling
  exact (ha coupling ((le_max_left _ _).trans hcoupling)).continuousWithinAt

/-- The critical phase grows sublinearly in the coupling. The stronger
assumption `0 < c.re` is unnecessary for this estimate. -/
theorem tendsto_logFlatSaddlePhase_inv_div {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    Tendsto (fun lam : ℝ => logFlatSaddlePhase β k tStar c lam⁻¹ / lam)
      atTop (𝓝 0) := by
  let C := 8 * β + |(k + 1) ^ 2 / (4 * β)|
  have hlog : Tendsto (fun lam : ℝ => (Real.log lam) ^ 2 / lam) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun lam : ℝ => C * ((Real.log lam) ^ 2 / lam))
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [(tendsto_inv_atTop_nhdsGT_zero.eventually
      (eventually_norm_logFlatSaddle_value_le (k := k) hβ ht hc)),
      eventually_gt_atTop (0 : ℝ)] with lam hv hlam
    simp only [one_div, inv_inv] at hv
    rw [norm_div, Real.norm_of_nonneg hlam.le]
    have him : ‖logFlatSaddlePhase β k tStar c lam⁻¹‖ ≤ C * (Real.log lam) ^ 2 := by
      simpa only [logFlatSaddlePhase, norm_neg, Real.norm_eq_abs, logFlatSaddleValue]
        using (Complex.abs_im_le_norm _).trans hv
    calc
      _ ≤ (C * (Real.log lam) ^ 2) / lam := div_le_div_of_nonneg_right him hlam.le
      _ = _ := by ring
  · simpa only [mul_zero] using hlog.const_mul C

/-- The Gaussian leading term for the normal integral at the actual saddle. -/
def logFlatSaddleLeading (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℂ :=
  ((tStar ^ (k + 1) * Real.sqrt (Real.pi /
    (β * (logFlatSaddleRoot β k tStar c h).re)) : ℝ) : ℂ) *
      Complex.exp (-logFlatSaddleValue β k tStar c h)

def logFlatSaddleLeadingSize (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℝ :=
  tStar ^ (k + 1) * Real.sqrt (Real.pi /
    (β * (logFlatSaddleRoot β k tStar c h).re)) *
      Real.exp (-(logFlatSaddleValue β k tStar c h).re)

/-- Exact amplitude-phase decomposition, with a single explicit real phase. -/
theorem logFlatSaddleLeading_eq_size_mul_phase (β k tStar : ℝ) (c : ℂ) (h : ℝ) :
    logFlatSaddleLeading β k tStar c h =
      (logFlatSaddleLeadingSize β k tStar c h : ℂ) *
        Complex.exp ((logFlatSaddlePhase β k tStar c h : ℂ) * Complex.I) := by
  unfold logFlatSaddleLeading logFlatSaddleLeadingSize logFlatSaddlePhase
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  congr 1
  simpa only [Complex.ofReal_neg, neg_mul, ← neg_add] using
    congrArg Neg.neg (Complex.re_add_im (logFlatSaddleValue β k tStar c h)).symm

theorem eventually_logFlatSaddleLeadingSize_pos {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < logFlatSaddleLeadingSize β k tStar c h := by
  filter_upwards [eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc]
    with h hw
  have hre : 0 < (logFlatSaddleRoot β k tStar c h).re := by linarith [hw.1]
  unfold logFlatSaddleLeadingSize
  positivity

end InfiniteZero
