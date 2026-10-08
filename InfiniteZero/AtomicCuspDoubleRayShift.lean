import InfiniteZero.AtomicCuspRayShift
import InfiniteZero.LogFlatMultiplierConnector
import InfiniteZero.DoubleIntegralFiberBound
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Relative control of the double physical contour displacement

All hybrid horizontal contours are absolutely integrable. The two
fiberwise contour identities then control the difference of the true
double integrals by the favorable left-connector error.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval

namespace InfiniteZero.CuspParameters

def atomicCuspLogProduct (p : CuspParameters) (L h s r η ξ : ℝ) (q : ℝ × ℝ) : ℂ :=
  let z := (q.1 : ℂ) + (η : ℂ) * Complex.I
  let w := (q.2 : ℂ) + (ξ : ℂ) * Complex.I
  logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h z *
    logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h w *
    p.frozenCuspKernelPhaseProfile L h
      (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹) s r
      ((p.tStar : ℂ) * Complex.exp (-z)) ((p.tStar : ℂ) * Complex.exp (-w))

def atomicCuspLogDoubleIntegral (p : CuspParameters) (L h s r η ξ : ℝ) : ℂ :=
  ∫ q in Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h),
    p.atomicCuspLogProduct L h s r η ξ q ∂(volume : Measure ℝ).prod volume

/-- Joint continuity on every horizontal product of truncated rays. -/
theorem eventually_continuousOn_atomicCuspLogProduct_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ → ∀ η ξ : ℝ,
      ContinuousOn (p.atomicCuspLogProduct L h s r η ξ)
        (Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h)) := by
  obtain ⟨ρ, hρ, hhol⟩ := exists_uniform_frozenCuspKernelPhaseProfile_bidisc hp hL
  obtain ⟨T, _hT, henergies⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  filter_upwards [(tendsto_logFlatActiveWindow p.tStar).eventually (gt_mem_nhds hρ),
    tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T), self_mem_nhdsWithin]
    with h hw hT hh
  intro s r hs hr η ξ
  have hE := henergies h⁻¹ hT
  simp only [inv_inv] at hE
  have hEc : 0 < -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹) := by
    linarith [hE.2.1.1]
  have hEf : 0 < scaledAtomicEnergy p h⁻¹ := by linarith [hE.1.1]
  have ha := (hhol s r hs hr h hh _ hEc _ hEf).continuousOn
  let P : ℝ × ℝ → Geometry.ComplexPoint := fun q =>
    ((p.tStar : ℂ) * Complex.exp (-((q.1 : ℂ) + (η : ℂ) * Complex.I)),
     (p.tStar : ℂ) * Complex.exp (-((q.2 : ℂ) + (ξ : ℂ) * Complex.I)))
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hmap : MapsTo P (Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h))
      (Metric.ball (0 : ℂ) ρ ×ˢ Metric.ball (0 : ℂ) ρ) := by
    intro q hq
    constructor
    · simpa only [P, Metric.mem_ball, dist_zero_right] using
        (norm_logarithmicPoint_le_activeWindow (hp.t₀_pos.trans hp.t₀_lt) hq.1.le η).trans_lt hw
    · simpa only [P, Metric.mem_ball, dist_zero_right] using
        (norm_logarithmicPoint_le_activeWindow (hp.t₀_pos.trans hp.t₀_lt) hq.2.le ξ).trans_lt hw
  have hc := ha.comp hP.continuousOn hmap
  have hg : Continuous (fun q : ℝ × ℝ =>
      logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
          ((q.1 : ℂ) + (η : ℂ) * Complex.I) *
        logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
          ((q.2 : ℂ) + (ξ : ℂ) * Complex.I)) := by
    unfold logFlatContourFunction logFlatComplexPhase
    fun_prop
  simpa only [atomicCuspLogProduct, P, Function.comp_apply] using hg.continuousOn.mul hc

/-- Absolute convergence of every hybrid contour between the real and
saddle rays, proved with the same fixed Gaussian in both coordinates. -/
theorem eventually_integrableOn_atomicCuspLogProduct_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ η ∈ uIcc 0 (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).im,
      ∀ ξ ∈ uIcc 0 (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).im,
        IntegrableOn (p.atomicCuspLogProduct L h s r η ξ)
          (Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h))
          ((volume : Measure ℝ).prod volume) := by
  have ht := hp.t₀_pos.trans hp.t₀_lt
  have hc := activeSaddleSlope_re_pos hp L
  have hcne := activeSaddleSlope_ne_zero hp L
  filter_upwards [eventually_continuousOn_atomicCuspLogProduct_of_radialData
    hp hRad hAcore hApot hL,
    eventually_norm_atomic_frozenCuspKernelPhaseProfile_le_two_of_radialData
      hp hRad hAcore hApot hL (by norm_num : (0 : ℝ) ≤ 1),
    eventually_logFlatSaddleRoot_connector_re (k := (2 : ℝ)) hp.β_pos ht hc,
    eventually_logFlatSaddleRoot_arg (k := (2 : ℝ)) hp.β_pos ht hcne,
    self_mem_nhdsWithin] with h hcont hbound hrot harg hh
  intro s r hs hr η hη ξ hξ
  have hv : |(logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).im| ≤ Real.pi :=
    harg.2.2.trans (Complex.abs_arg_le_pi _)
  have hηabs : |η| ≤ Real.pi :=
    (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hη : |η| ≤ _).trans hv
  have hξabs : |ξ| ≤ Real.pi :=
    (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hξ : |ξ| ≤ _).trans hv
  have hgη := integrable_logFlatContourFunction_horizontal hp.β_pos ht.le hh hηabs
    (hc.le.trans (hrot η hη)) (2 : ℝ)
  have hgξ := integrable_logFlatContourFunction_horizontal hp.β_pos ht.le hh hξabs
    (hc.le.trans (hrot ξ hξ)) (2 : ℝ)
  have hmajor := ((hgη.norm.mul_prod hgξ.norm).const_mul 2).integrableOn
    (s := Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h))
  apply hmajor.mono' ((hcont s r hs hr η ξ).aestronglyMeasurable
    (measurableSet_Ioi.prod measurableSet_Ioi))
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with q hq
  have hb := hbound s r hs hr
    ((p.tStar : ℂ) * Complex.exp (-((q.1 : ℂ) + (η : ℂ) * Complex.I)))
    ((p.tStar : ℂ) * Complex.exp (-((q.2 : ℂ) + (ξ : ℂ) * Complex.I)))
    (by simpa only [one_mul] using norm_logarithmicPoint_le_activeWindow ht hq.1.le η)
    (by simpa only [one_mul] using norm_logarithmicPoint_le_activeWindow ht hq.2.le ξ)
  dsimp only [atomicCuspLogProduct]
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (‖logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
        ((q.1 : ℂ) + (η : ℂ) * Complex.I)‖ *
      ‖logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
        ((q.2 : ℂ) + (ξ : ℂ) * Complex.I)‖) * 2 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Factoring the fixed second scalar factor in the first integration. -/
theorem atomicCuspLogProduct_integral_first (p : CuspParameters) (L h s r η ξ y : ℝ) :
    (∫ x in Ioi (logFlatActiveLogCut h), p.atomicCuspLogProduct L h s r η ξ (x, y)) =
      logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
        ((y : ℂ) + (ξ : ℂ) * Complex.I) *
      (∫ x in Ioi (logFlatActiveLogCut h),
        logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
          ((x : ℂ) + (η : ℂ) * Complex.I) *
        p.atomicCuspLogMultiplier L h s r
          ((p.tStar : ℂ) * Complex.exp (-((y : ℂ) + (ξ : ℂ) * Complex.I)))
          ((x : ℂ) + (η : ℂ) * Complex.I)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [atomicCuspLogProduct, atomicCuspLogMultiplier]
  ring

/-- Factoring the fixed first scalar factor in the second integration. -/
theorem atomicCuspLogProduct_integral_second (p : CuspParameters) (L h s r η ξ x : ℝ) :
    (∫ y in Ioi (logFlatActiveLogCut h), p.atomicCuspLogProduct L h s r η ξ (x, y)) =
      logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
        ((x : ℂ) + (η : ℂ) * Complex.I) *
      (∫ y in Ioi (logFlatActiveLogCut h),
        logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
          ((y : ℂ) + (ξ : ℂ) * Complex.I) *
        p.atomicCuspLogMultiplierSecond L h s r
          ((p.tStar : ℂ) * Complex.exp (-((x : ℂ) + (η : ℂ) * Complex.I)))
          ((y : ℂ) + (ξ : ℂ) * Complex.I)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [atomicCuspLogProduct, atomicCuspLogMultiplierSecond]
  ring

/-- The two exact fiber shifts yield a uniformly stretched-exponentially
small difference of the genuine double integrals. -/
theorem exists_atomicCuspLogDoubleIntegral_shift_bound_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      let v := (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).im
      ‖p.atomicCuspLogDoubleIntegral L h s r 0 0 -
        p.atomicCuspLogDoubleIntegral L h s r v v‖ ≤
        C * Real.exp (-(p.tStar * (p.activeSaddleSlope L).re) *
          Real.exp ((1 / 4 : ℝ) * Real.log (1 / h))) := by
  let A := logFlatErrorMajorant p.β 2
  let g : ℝ → ℝ := fun x => A * Real.exp (-(p.β / 2) * x ^ 2)
  have hA : 0 < A := Real.exp_pos _
  have hg : Integrable g := (integrable_exp_neg_mul_sq (half_pos hp.β_pos)).const_mul A
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg hA.le (Real.exp_pos _).le
  let J := ∫ x, g x
  have hJ0 : 0 ≤ J := integral_nonneg hg0
  refine ⟨4 * Real.pi * A * (J + 1), by positivity, ?_⟩
  have ht := hp.t₀_pos.trans hp.t₀_lt
  have hc := activeSaddleSlope_re_pos hp L
  filter_upwards [eventually_integrableOn_atomicCuspLogProduct_of_radialData
    hp hRad hAcore hApot hL,
    eventually_atomicCuspLogMultiplier_properties_of_radialData hp hRad hAcore hApot hL,
    eventually_atomicCuspLogMultiplier_ray_shift_of_radialData hp hRad hAcore hApot hL,
    eventually_atomicCuspLogMultiplierSecond_ray_shift_of_radialData hp hRad hAcore hApot hL,
    eventually_logFlatActive_multiplier_connector_le (k := (2 : ℝ)) hp.β_pos ht hc,
    eventually_logFlatSaddleRoot_connector_re (k := (2 : ℝ)) hp.β_pos ht hc,
    eventually_logFlatSaddleRoot_arg (k := (2 : ℝ)) hp.β_pos ht (activeSaddleSlope_ne_zero hp L),
    self_mem_nhdsWithin] with h hi hprop hshift₁ hshift₂ hconnector hrot harg hh
  intro s r hs hr
  let v := (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).im
  let a := logFlatActiveLogCut h
  let μ : Measure ℝ := volume.restrict (Ioi a)
  let e := Real.exp (-(p.tStar * (p.activeSaddleSlope L).re) *
    Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)))
  let D := Real.pi * A * 2 * e
  have hD : 0 ≤ D := by dsimp [D, e]; positivity
  have hgauss (η : ℝ) (hη : η ∈ uIcc 0 v) (x : ℝ) :
      ‖logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h
        ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤ g x := by
    apply norm_logFlatContourFunction_le_gaussian hp.β_pos ht.le hh
    · have hav : |v| ≤ Real.pi := harg.2.2.trans (Complex.abs_arg_le_pi _)
      exact (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hη : |η| ≤ |v|).trans hav
    · exact hc.le.trans (hrot η hη)
  have hfirst (y : ℝ) (hy : y ∈ Ioi a) :
      ‖(∫ x, p.atomicCuspLogProduct L h s r 0 0 (x, y) ∂μ) -
        ∫ x, p.atomicCuspLogProduct L h s r v 0 (x, y) ∂μ‖ ≤ D * g y := by
    let u := (p.tStar : ℂ) * Complex.exp (-(y : ℂ))
    have hu : ‖u‖ ≤ logFlatActiveWindow p.tStar h := by
      simpa only [u, Complex.ofReal_zero, zero_mul, add_zero] using
        norm_logarithmicPoint_le_activeWindow ht hy.le (0 : ℝ)
    have he := (hshift₁ s r hs hr u hu v).2.2
    have hb := hconnector 2 (by norm_num) (p.atomicCuspLogMultiplier L h s r u)
      (fun η hη => (hprop s r hs hr u hu v).2.1 _ (mem_logFlatContourHalfStrip le_rfl hη))
    change ‖_‖ ≤ D at hb
    change ‖(∫ x in Ioi a, _) - ∫ x in Ioi a, _‖ ≤ _
    rw [atomicCuspLogProduct_integral_first, atomicCuspLogProduct_integral_first, ← mul_sub]
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at he ⊢
    have hd := sub_eq_iff_eq_add.mpr he
    rw [hd, norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc
      _ ≤ g y * D := mul_le_mul (by simpa using hgauss 0 left_mem_uIcc y) hb
        (norm_nonneg _) (hg0 y)
      _ = _ := mul_comm _ _
  have hsecond (x : ℝ) (hx : x ∈ Ioi a) :
      ‖(∫ y, p.atomicCuspLogProduct L h s r v 0 (x, y) ∂μ) -
        ∫ y, p.atomicCuspLogProduct L h s r v v (x, y) ∂μ‖ ≤ D * g x := by
    let t := (p.tStar : ℂ) * Complex.exp (-((x : ℂ) + (v : ℂ) * Complex.I))
    have ht' : ‖t‖ ≤ logFlatActiveWindow p.tStar h :=
      norm_logarithmicPoint_le_activeWindow ht hx.le v
    have he := (hshift₂ s r hs hr t ht' v).2.2
    have hb := hconnector 2 (by norm_num) (p.atomicCuspLogMultiplierSecond L h s r t)
      (fun η hη => (hprop s r hs hr t ht' v).2.2.2 _ (mem_logFlatContourHalfStrip le_rfl hη))
    change ‖_‖ ≤ D at hb
    change ‖(∫ y in Ioi a, _) - ∫ y in Ioi a, _‖ ≤ _
    rw [atomicCuspLogProduct_integral_second, atomicCuspLogProduct_integral_second, ← mul_sub]
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at he ⊢
    have hd := sub_eq_iff_eq_add.mpr he
    rw [hd, norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc
      _ ≤ g x * D := mul_le_mul (hgauss v right_mem_uIcc x) hb (norm_nonneg _) (hg0 x)
      _ = _ := mul_comm _ _
  have hi00 : Integrable (p.atomicCuspLogProduct L h s r 0 0) (μ.prod μ) := by
    simpa only [μ, a, IntegrableOn, Measure.prod_restrict] using
      hi s r hs hr 0 left_mem_uIcc 0 left_mem_uIcc
  have hiv0 : Integrable (p.atomicCuspLogProduct L h s r v 0) (μ.prod μ) := by
    simpa only [μ, a, IntegrableOn, Measure.prod_restrict] using
      hi s r hs hr v right_mem_uIcc 0 left_mem_uIcc
  have hivv : Integrable (p.atomicCuspLogProduct L h s r v v) (μ.prod μ) := by
    simpa only [μ, a, IntegrableOn, Measure.prod_restrict] using
      hi s r hs hr v right_mem_uIcc v right_mem_uIcc
  have hnorm₁ := norm_integral_prod_sub_le_of_fiber_integral_sub_bound hi00 hiv0
    (hg.integrableOn (s := Ioi a)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hfirst y hy)
  have hnorm₂ := norm_integral_prod_sub_le_of_fiber_integral_sub_bound_left hiv0 hivv
    (hg.integrableOn (s := Ioi a)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hsecond x hx)
  have hJ : (∫ x in Ioi a, g x) ≤ J + 1 :=
    (setIntegral_le_integral hg (Eventually.of_forall hg0)).trans (by linarith)
  have hn₁ : ‖p.atomicCuspLogDoubleIntegral L h s r 0 0 -
      p.atomicCuspLogDoubleIntegral L h s r v 0‖ ≤ D * (J + 1) := by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left hJ hD)
    simpa only [atomicCuspLogDoubleIntegral, μ, a, Measure.prod_restrict] using hnorm₁
  have hn₂ : ‖p.atomicCuspLogDoubleIntegral L h s r v 0 -
      p.atomicCuspLogDoubleIntegral L h s r v v‖ ≤ D * (J + 1) := by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left hJ hD)
    simpa only [atomicCuspLogDoubleIntegral, μ, a, Measure.prod_restrict] using hnorm₂
  calc
    _ = ‖(p.atomicCuspLogDoubleIntegral L h s r 0 0 -
        p.atomicCuspLogDoubleIntegral L h s r v 0) +
        (p.atomicCuspLogDoubleIntegral L h s r v 0 -
          p.atomicCuspLogDoubleIntegral L h s r v v)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ D * (J + 1) + D * (J + 1) := add_le_add hn₁ hn₂
    _ = _ := by dsimp [D, e]; ring

/-- The actual double contour displacement is negligible after the square
of the complex saddle normalizer, uniformly in both tangential parameters. -/
theorem eventually_atomicCuspLogDoubleIntegral_shift_error_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      let v := (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).im
      ‖(logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h) ^ 2 *
        (p.atomicCuspLogDoubleIntegral L h s r 0 0 -
          p.atomicCuspLogDoubleIntegral L h s r v v)‖ < ε := by
  obtain ⟨C, _hC, herror⟩ := exists_atomicCuspLogDoubleIntegral_shift_bound_of_radialData
    hp hRad hAcore hApot hL
  let d := p.tStar * (p.activeSaddleSlope L).re
  have hd : 0 < d := mul_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_re_pos hp L)
  have hhalf := tendsto_logFlatSaddle_normalized_stretched_error (k := (2 : ℝ))
    hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L)
    (half_pos hd) (by norm_num : (0 : ℝ) < 1 / 4)
  have hidentity (h : ℝ) :
      (‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h‖ *
        Real.exp (-(d / 2) * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)))) ^ 2 =
      ‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h‖ ^ 2 *
        Real.exp (-d * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h))) := by
    rw [mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsmall : Tendsto (fun h : ℝ => C *
      (‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h‖ ^ 2 *
        Real.exp (-d * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h))))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hidentity, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] using
      (hhalf.pow 2).const_mul C
  filter_upwards [herror, hsmall.eventually (gt_mem_nhds hε)] with h he hsmallh
  intro s r hs hr
  dsimp only
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h‖ ^ 2 *
        (C * Real.exp (-d * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)))) :=
      mul_le_mul_of_nonneg_left (he s r hs hr) (sq_nonneg _)
    _ = C * (‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h‖ ^ 2 *
        Real.exp (-d * Real.exp ((1 / 4 : ℝ) * Real.log (1 / h)))) := by ring
    _ < ε := hsmallh

end InfiniteZero.CuspParameters
