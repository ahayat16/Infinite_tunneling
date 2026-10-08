import InfiniteZero.LogFlatActiveWindow

/-!
# The real normal tail outside the shrinking active window

For every real slope above a fixed positive lower bound, the integral on
`[tStar * h^(3/4), t₀)` has stretched exponential decay. This estimate is
uniform in the slope and survives normalization by any fixed nonzero
complex reference slope.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InfiniteZero

def logFlatActiveRealTail (β tStar t₀ A h : ℝ) (m : ℕ) : ℝ :=
  ∫ t in Ico (logFlatActiveWindow tStar h) t₀,
    t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - A * t / h)

theorem logFlatActiveRealTail_nonneg {tStar : ℝ} (ht : 0 < tStar)
    (β t₀ A h : ℝ) (m : ℕ) : 0 ≤ logFlatActiveRealTail β tStar t₀ A h m := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t hmem
  have htpos : 0 < t := (logFlatActiveWindow_pos ht h).trans_le hmem.1
  exact mul_nonneg (pow_nonneg htpos.le m) (Real.exp_pos _).le

theorem integrableOn_logFlatActiveRealTail {β tStar : ℝ}
    (hβ : 0 < β) (ht : 0 < tStar) (t₀ A h : ℝ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ m *
      Real.exp (-β * (Real.log (tStar / t)) ^ 2 - A * t / h))
        (Ico (logFlatActiveWindow tStar h) t₀) := by
  apply (integrableOn_logFlat_laplace hβ ht t₀ A h m).mono_set
  intro t hmem
  exact ⟨(logFlatActiveWindow_pos ht h).trans_le hmem.1, hmem.2⟩

/-- A finite-parameter bound valid whenever the active window is below `t₀`. -/
theorem logFlatActiveRealTail_le {β tStar t₀ A₀ A h : ℝ}
    (hβ : 0 < β) (ht : 0 < tStar) (hA₀ : 0 < A₀) (hA : A₀ ≤ A)
    (hh : 0 < h) (hwindow : logFlatActiveWindow tStar h < t₀) (m : ℕ) :
    logFlatActiveRealTail β tStar t₀ A h m ≤
      t₀ ^ (m + 1) * Real.exp (-(A₀ * tStar) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h))) := by
  let T := logFlatActiveWindow tStar h
  have hT : 0 < T := logFlatActiveWindow_pos ht h
  have ht₀ : 0 < t₀ := hT.trans hwindow
  let K := t₀ ^ m * Real.exp (-A₀ * T / h)
  have hbound (t : ℝ) (hmem : t ∈ Ico T t₀) :
      t ^ m * Real.exp (-β * (Real.log (tStar / t)) ^ 2 - A * t / h) ≤ K := by
    have htpos : 0 < t := hT.trans_le hmem.1
    have hAt : A₀ * T / h ≤ A * t / h := by
      apply div_le_div_of_nonneg_right _ hh.le
      exact mul_le_mul hA hmem.1 hT.le (hA₀.le.trans hA)
    have hexp : Real.exp (-β * (Real.log (tStar / t)) ^ 2 - A * t / h) ≤
        Real.exp (-A₀ * T / h) := by
      apply Real.exp_le_exp.mpr
      have hs := mul_nonneg hβ.le (sq_nonneg (Real.log (tStar / t)))
      simp only [neg_mul, neg_div]
      linarith
    exact mul_le_mul (pow_le_pow_left₀ htpos.le hmem.2.le m) hexp
      (Real.exp_pos _).le (pow_nonneg ht₀.le m)
  have hconst : IntegrableOn (fun _ : ℝ => K) (Ico T t₀) :=
    (continuous_const.continuousOn.integrableOn_Icc (a := T) (b := t₀)).mono_set
      Ico_subset_Icc_self
  have hint := setIntegral_mono_on (integrableOn_logFlatActiveRealTail hβ ht t₀ A h m)
    hconst measurableSet_Ico hbound
  have he : -A₀ * T / h =
      -(A₀ * tStar) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)) := by
    calc
      _ = -A₀ * (logFlatActiveWindow tStar h / h) := by dsimp [T]; ring
      _ = _ := by rw [logFlatActiveWindow_div tStar hh]; ring
  calc
    _ ≤ ∫ _t in Ico T t₀, K := hint
    _ = (t₀ - T) * K := by
      rw [setIntegral_const, Real.volume_real_Ico,
        max_eq_left (sub_nonneg.mpr hwindow.le), smul_eq_mul]
    _ ≤ t₀ * K := mul_le_mul_of_nonneg_right (by linarith) (by dsimp [K]; positivity)
    _ = _ := by dsimp [K]; rw [he, pow_succ]; ring

/-- The threshold in `h` is independent of the slope `A ≥ A₀`. -/
theorem eventually_logFlatActiveRealTail_le {β tStar t₀ A₀ : ℝ}
    (hβ : 0 < β) (ht : 0 < tStar) (ht₀ : 0 < t₀) (hA₀ : 0 < A₀) (m : ℕ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ A : ℝ, A₀ ≤ A →
      logFlatActiveRealTail β tStar t₀ A h m ≤
        t₀ ^ (m + 1) * Real.exp (-(A₀ * tStar) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h))) := by
  filter_upwards [(tendsto_logFlatActiveWindow tStar).eventually (gt_mem_nhds ht₀),
    self_mem_nhdsWithin] with h hw hh
  exact fun A hA => logFlatActiveRealTail_le hβ ht hA₀ hA hh hw m

/-- Negligibility after the actual complex saddle normalization, uniform over
the entire half-line of real slopes. The reference slope is fixed. -/
theorem tendstoUniformlyOn_logFlatActiveRealTail_normalized
    {β k tStar t₀ A₀ : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (ht₀ : 0 < t₀) (hA₀ : 0 < A₀)
    (hc : c ≠ 0) (m : ℕ) :
    TendstoUniformlyOn (fun h A : ℝ => ‖logFlatSaddleNormalizer β k tStar c h‖ *
      logFlatActiveRealTail β tStar t₀ A h m) (fun _ => 0) (𝓝[>] 0) (Ici A₀) := by
  have hdecay := (tendsto_logFlatSaddle_normalized_stretched_error (k := k)
    hβ ht hc (mul_pos hA₀ ht) (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul (t₀ ^ (m + 1))
  simp only [mul_zero] at hdecay
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_logFlatActiveRealTail_le hβ ht ht₀ hA₀ m,
    hdecay.eventually (gt_mem_nhds hε)] with h hb hsmall
  intro A hA
  have hnonneg : 0 ≤ ‖logFlatSaddleNormalizer β k tStar c h‖ *
      logFlatActiveRealTail β tStar t₀ A h m :=
    mul_nonneg (norm_nonneg _) (logFlatActiveRealTail_nonneg ht β t₀ A h m)
  have hbound : ‖logFlatSaddleNormalizer β k tStar c h‖ *
      logFlatActiveRealTail β tStar t₀ A h m ≤
      t₀ ^ (m + 1) * (‖logFlatSaddleNormalizer β k tStar c h‖ *
        Real.exp (-(A₀ * tStar) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)))) := by
    calc
      _ ≤ ‖logFlatSaddleNormalizer β k tStar c h‖ *
          (t₀ ^ (m + 1) * Real.exp (-(A₀ * tStar) *
            Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)))) :=
        mul_le_mul_of_nonneg_left (hb A hA) (norm_nonneg _)
      _ = _ := by ring
  simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    using hbound.trans_lt hsmall

/-- The real slope may depend on `h`, without a continuity or an upper-bound
assumption, provided it eventually stays above the same positive lower bound. -/
theorem tendsto_logFlatActiveRealTail_normalized {β k tStar t₀ A₀ : ℝ}
    {c : ℂ} {A : ℝ → ℝ} (hβ : 0 < β) (ht : 0 < tStar) (ht₀ : 0 < t₀)
    (hA₀ : 0 < A₀) (hc : c ≠ 0) (m : ℕ)
    (hA : ∀ᶠ h : ℝ in 𝓝[>] 0, A₀ ≤ A h) :
    Tendsto (fun h : ℝ => ‖logFlatSaddleNormalizer β k tStar c h‖ *
      logFlatActiveRealTail β tStar t₀ (A h) h m) (𝓝[>] 0) (𝓝 0) := by
  have hu := tendstoUniformlyOn_logFlatActiveRealTail_normalized
    (k := k) hβ ht ht₀ hA₀ hc m
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε, hA] with h hh hAh
  simpa only [dist_comm] using hh (A h) hAh

end InfiniteZero
