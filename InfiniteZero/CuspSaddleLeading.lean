import InfiniteZero.CuspSaddleMultiplier

/-!
# Evaluation on the actual truncated product saddle contour

The discarded left horizontal tail is negligible after saddle normalization.
The two logarithmic normal integrals therefore have normalized product limit
π/β. The proved multiplier error transfers this limit to the true kernel
profile, uniformly in the real tangent parameters. These are logarithmic
integrals: the physical factor tStar^6 belongs to a later change of variables.
No deformation of the physical cell is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

/-- The horizontal saddle ray restricted to the actual active normal window. -/
def logFlatSaddleActiveIntegral (β k tStar : ℝ) (c : ℂ) (h : ℝ) : ℂ :=
  ∫ q in Ioi (logFlatActiveLogCut h -
    (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)).re),
    logFlatSaddleContourIntegrand β k tStar c h q

/-- Exact real translation of the left tail to logarithmic coordinates. -/
theorem integral_logFlatSaddleContour_left (β k tStar : ℝ) (c : ℂ) (h a : ℝ) :
    (∫ q in Iic (a -
      (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)).re),
      logFlatSaddleContourIntegrand β k tStar c h q) =
    ∫ x in Iic a, logFlatContourFunction β k tStar c h
      ((x : ℂ) + ((logFlatSaddleRoot β k tStar c h).im : ℂ) * Complex.I) := by
  let w := logFlatSaddleRoot β k tStar c h
  let z := logFlatComplexCritical β k w
  have he (q : ℝ) : z + (q : ℂ) =
      ((q + z.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
    have hi : z.im = w.im := by
      simp only [z, logFlatComplexCritical, Complex.sub_im, Complex.ofReal_im, sub_zero]
    apply Complex.ext <;> simp [hi, add_comm]
  have hpre : (fun q : ℝ => q + z.re) ⁻¹' Iic a = Iic (a - z.re) := by
    ext q
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro hq <;> linarith
  have hi := (measurePreserving_add_right (volume : Measure ℝ) z.re).setIntegral_preimage_emb
    (MeasurableEquiv.addRight z.re).measurableEmbedding
    (fun x : ℝ => logFlatContourFunction β k tStar c h
      ((x : ℂ) + (w.im : ℂ) * Complex.I)) (Iic a)
  rw [hpre] at hi
  change (∫ q in Iic (a - z.re),
    Complex.exp (-logFlatComplexPhase β k (c * (tStar : ℂ) / (h : ℂ))
      (z + (q : ℂ)))) = _
  simp_rw [he]
  exact hi

/-- The left portion discarded from the full horizontal saddle is negligible
at the actual saddle scale, even though the cutoff moves with h. -/
theorem tendsto_logFlatSaddle_active_left_normalized
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer β k tStar c h *
      (∫ q in Iic (logFlatActiveLogCut h -
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)).re),
        logFlatSaddleContourIntegrand β k tStar c h q))
      (𝓝[>] 0) (𝓝 0) := by
  have hcne : c ≠ 0 := by intro hz; simp [hz] at hc
  apply tendsto_logFlatSaddle_normalized_stretched_remainder hβ ht hcne
    (mul_pos ht hc) (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [eventually_logFlatSaddleRoot_connector_re (k := k) hβ ht hc,
    eventually_logFlatSaddleRoot_arg (k := k) hβ ht hcne, self_mem_nhdsWithin]
    with h hrot harg hh
  have hv : |(logFlatSaddleRoot β k tStar c h).im| ≤ Real.pi :=
    harg.2.2.trans (Complex.abs_arg_le_pi c)
  rw [integral_logFlatSaddleContour_left]
  have hb := norm_integral_logFlatContourFunction_left_le hβ ht hh hv hc
    (hrot _ right_mem_uIcc) k (logFlatActiveLogCut h)
  simpa only [neg_div, logFlatActiveWindow_error_rate tStar c hh, neg_mul] using hb

/-- Leading value of the truncated one-dimensional logarithmic saddle ray. -/
theorem tendsto_logFlatSaddle_active_leading
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    Tendsto (fun h : ℝ => logFlatSaddleNormalizer β k tStar c h *
      logFlatSaddleActiveIntegral β k tStar c h)
      (𝓝[>] 0) (𝓝 ((Real.sqrt (Real.pi / β) : ℝ) : ℂ)) := by
  have hcne : c ≠ 0 := by intro hz; simp [hz] at hc
  have hlim := (tendsto_logFlatSaddle_horizontal_leading (k := k) hβ ht hcne).sub
    (tendsto_logFlatSaddle_active_left_normalized (k := k) hβ ht hc)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_integrable_logFlatSaddleHorizontal (k := k) hβ ht hcne]
    with h hi
  have hs := integral_add_compl
    (s := Iic (logFlatActiveLogCut h -
      (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)).re))
    measurableSet_Iic hi
  simp only [compl_Iic] at hs
  change logFlatSaddleNormalizer β k tStar c h *
      (∫ q : ℝ, logFlatSaddleContourIntegrand β k tStar c h q) -
    logFlatSaddleNormalizer β k tStar c h *
      (∫ q in Iic (logFlatActiveLogCut h -
        (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)).re),
        logFlatSaddleContourIntegrand β k tStar c h q) = _
  change _ = logFlatSaddleNormalizer β k tStar c h *
    (∫ q in Ioi (logFlatActiveLogCut h -
      (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)).re),
      logFlatSaddleContourIntegrand β k tStar c h q)
  change (∫ q in Iic _, logFlatSaddleContourIntegrand β k tStar c h q) +
    (∫ q in Ioi _, logFlatSaddleContourIntegrand β k tStar c h q) =
    (∫ q, logFlatSaddleContourIntegrand β k tStar c h q) at hs
  linear_combination -(logFlatSaddleNormalizer β k tStar c h) * hs

/-- The actual truncated product has limit π/β after normalization by N².
No factor tStar^6 has yet been introduced by a physical substitution. -/
theorem tendsto_logFlatSaddleProduct_active_leading
    {β k tStar : ℝ} {c : ℂ} (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    Tendsto (fun h : ℝ => (logFlatSaddleNormalizer β k tStar c h) ^ 2 *
      (∫ q in activeSaddleProductDomain β k tStar c h,
        logFlatSaddleProductIntegrand β k tStar c c h q
          ∂(volume : Measure ℝ).prod volume))
      (𝓝[>] 0) (𝓝 ((Real.pi / β : ℝ) : ℂ)) := by
  have hlim := (tendsto_logFlatSaddle_active_leading (k := k) hβ ht hc).pow 2
  have hsq : (((Real.sqrt (Real.pi / β) : ℝ) : ℂ) ^ 2) = (Real.pi / β : ℝ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (div_pos Real.pi_pos hβ).le]
  rw [hsq] at hlim
  apply hlim.congr
  intro h
  unfold activeSaddleProductDomain logFlatSaddleProductIntegrand logFlatSaddleActiveIntegral
  rw [setIntegral_prod_mul]
  ring

namespace CuspParameters

/-- Uniform evaluation of the true incoming multiplier on the truncated
product saddle contour. The physical cell deformation is a separate step. -/
theorem eventually_atomicCuspSaddleProduct_leading_uniform_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ‖(logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h) ^ 2 *
        (∫ q in activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h,
          logFlatSaddleProductIntegrand p.β 2 p.tStar
            (p.activeSaddleSlope L) (p.activeSaddleSlope L) h q *
          p.atomicCuspSaddleMultiplier L h s r q ∂(volume : Measure ℝ).prod volume) -
        ((Real.pi / p.β : ℝ) : ℂ)‖ < ε := by
  have hm := tendsto_logFlatSaddleProduct_active_leading (k := (2 : ℝ))
    hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_re_pos hp L)
  have hmodel := (Metric.tendsto_nhds.mp hm) (ε / 2) (half_pos hε)
  have herror := eventually_atomicCuspSaddleMultiplier_integral_error_of_radialData
    hp hRad hAcore hApot hL (half_pos hε)
  filter_upwards [hmodel, herror] with h hmh heh
  intro s r hs hr
  have he := heh s r hs hr
  simp only [dist_eq_norm] at hmh
  let N := logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h
  let S := activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h
  let F := logFlatSaddleProductIntegrand p.β 2 p.tStar
    (p.activeSaddleSlope L) (p.activeSaddleSlope L) h
  let B := p.atomicCuspSaddleMultiplier L h s r
  change ‖N ^ 2 * ((∫ q in S, F q * B q ∂(volume : Measure ℝ).prod volume) -
    ∫ q in S, F q ∂(volume : Measure ℝ).prod volume)‖ < ε / 2 at he
  change ‖N ^ 2 * (∫ q in S, F q ∂(volume : Measure ℝ).prod volume) -
    ((Real.pi / p.β : ℝ) : ℂ)‖ < ε / 2 at hmh
  change ‖N ^ 2 * (∫ q in S, F q * B q ∂(volume : Measure ℝ).prod volume) -
    ((Real.pi / p.β : ℝ) : ℂ)‖ < ε
  have heq : N ^ 2 * (∫ q in S, F q * B q ∂(volume : Measure ℝ).prod volume) -
      ((Real.pi / p.β : ℝ) : ℂ) =
    N ^ 2 * ((∫ q in S, F q * B q ∂(volume : Measure ℝ).prod volume) -
      ∫ q in S, F q ∂(volume : Measure ℝ).prod volume) +
      (N ^ 2 * (∫ q in S, F q ∂(volume : Measure ℝ).prod volume) -
        ((Real.pi / p.β : ℝ) : ℂ)) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

end CuspParameters
end InfiniteZero
