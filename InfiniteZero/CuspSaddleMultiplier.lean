import InfiniteZero.CuspKernelProfileHolomorphic
import InfiniteZero.ComplexSaddleProduct
import InfiniteZero.LogFlatActiveTruncation

/-!
# The actual incoming multiplier on the truncated product saddle contour

The normal coordinates stay inside the active window. Continuity and
integrability are deduced from the genuine holomorphic kernel profile,
and its uniform error can then be inserted in the product saddle integral.
This is an estimate on the saddle contour; contour deformation is separate.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology

namespace InfiniteZero

def saddleNormalPoint (β k tStar : ℝ) (c : ℂ) (h q : ℝ) : ℂ :=
  (tStar : ℂ) * Complex.exp
    (-(logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h) + (q : ℂ)))

def activeSaddleProductDomain (β k tStar : ℝ) (c : ℂ) (h : ℝ) : Set (ℝ × ℝ) :=
  let a := logFlatActiveLogCut h - (logFlatComplexCritical β k
    (logFlatSaddleRoot β k tStar c h)).re
  Ioi a ×ˢ Ioi a

theorem measurableSet_activeSaddleProductDomain (β k tStar : ℝ) (c : ℂ) (h : ℝ) :
    MeasurableSet (activeSaddleProductDomain β k tStar c h) :=
  measurableSet_Ioi.prod measurableSet_Ioi

theorem continuous_saddleNormalPoint (β k tStar : ℝ) (c : ℂ) (h : ℝ) :
    Continuous (saddleNormalPoint β k tStar c h) := by
  unfold saddleNormalPoint
  fun_prop

theorem norm_saddleNormalPoint_le_activeWindow {tStar : ℝ} (htStar : 0 < tStar)
    (β k : ℝ) (c : ℂ) (h q : ℝ)
    (hq : logFlatActiveLogCut h -
      (logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)).re < q) :
    ‖saddleNormalPoint β k tStar c h q‖ ≤ logFlatActiveWindow tStar h := by
  let z := logFlatComplexCritical β k (logFlatSaddleRoot β k tStar c h)
  have he : z + (q : ℂ) = ((z.re + q : ℝ) : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  unfold saddleNormalPoint
  change ‖(tStar : ℂ) * Complex.exp (-(z + (q : ℂ)))‖ ≤ _
  rw [he]
  exact norm_logarithmicPoint_le_activeWindow htStar (by dsimp [z]; linarith) z.im

namespace CuspParameters

def atomicCuspSaddleMultiplier (p : CuspParameters) (L h s r : ℝ) (q : ℝ × ℝ) : ℂ :=
  p.frozenCuspKernelPhaseProfile L h
    (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹) s r
    (saddleNormalPoint p.β 2 p.tStar (p.activeSaddleSlope L) h q.1)
    (saddleNormalPoint p.β 2 p.tStar (p.activeSaddleSlope L) h q.2)

theorem eventually_atomicCuspSaddleMultiplier_uniform_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ q ∈ activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h,
        ‖p.atomicCuspSaddleMultiplier L h s r q - 1‖ < ε := by
  filter_upwards [eventually_atomic_frozenCuspKernelPhaseProfile_uniform_of_radialData
    hp hRad hAcore hApot hL (by norm_num : (0 : ℝ) ≤ 1) hε] with h hh
  intro s r hs hr q hq
  apply hh s r hs hr
  · simpa only [one_mul] using norm_saddleNormalPoint_le_activeWindow
      (hp.t₀_pos.trans hp.t₀_lt) p.β 2 (p.activeSaddleSlope L) h q.1 hq.1
  · simpa only [one_mul] using norm_saddleNormalPoint_le_activeWindow
      (hp.t₀_pos.trans hp.t₀_lt) p.β 2 (p.activeSaddleSlope L) h q.2 hq.2

theorem eventually_norm_atomicCuspSaddleMultiplier_le_two_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ q ∈ activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h,
        ‖p.atomicCuspSaddleMultiplier L h s r q‖ ≤ 2 := by
  filter_upwards [eventually_atomicCuspSaddleMultiplier_uniform_of_radialData
    hp hRad hAcore hApot hL (by norm_num : (0 : ℝ) < 1)] with h hh
  intro s r hs hr q hq
  have he := hh s r hs hr q hq
  have hn := norm_sub_le (p.atomicCuspSaddleMultiplier L h s r q - 1) (-1)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at hn
  linarith

theorem eventually_continuousOn_atomicCuspSaddleMultiplier_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ContinuousOn (p.atomicCuspSaddleMultiplier L h s r)
        (activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h) := by
  obtain ⟨η, hη, hhol⟩ := exists_uniform_frozenCuspKernelPhaseProfile_bidisc hp hL
  obtain ⟨T, _hT, henergies⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  have hw := (tendsto_logFlatActiveWindow p.tStar).eventually (gt_mem_nhds hη)
  filter_upwards [hw, tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T),
    self_mem_nhdsWithin] with h hwindow hT hh
  intro s r hs hr
  have hE := henergies h⁻¹ hT
  simp only [inv_inv] at hE
  have hEc : 0 < -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹) := by
    linarith [hE.2.1.1]
  have hEf : 0 < scaledAtomicEnergy p h⁻¹ := by linarith [hE.1.1]
  have ha := hhol s r hs hr h hh _ hEc _ hEf
  let P : ℝ × ℝ → Geometry.ComplexPoint := fun q =>
    (saddleNormalPoint p.β 2 p.tStar (p.activeSaddleSlope L) h q.1,
      saddleNormalPoint p.β 2 p.tStar (p.activeSaddleSlope L) h q.2)
  have hP : Continuous P :=
    ((continuous_saddleNormalPoint _ _ _ _ _).comp continuous_fst).prodMk
      ((continuous_saddleNormalPoint _ _ _ _ _).comp continuous_snd)
  apply ha.continuousOn.comp hP.continuousOn
  intro q hq
  constructor
  · simpa only [P, Metric.mem_ball, dist_zero_right] using
      (norm_saddleNormalPoint_le_activeWindow (hp.t₀_pos.trans hp.t₀_lt)
        p.β 2 (p.activeSaddleSlope L) h q.1 hq.1).trans_lt hwindow
  · simpa only [P, Metric.mem_ball, dist_zero_right] using
      (norm_saddleNormalPoint_le_activeWindow (hp.t₀_pos.trans hp.t₀_lt)
        p.β 2 (p.activeSaddleSlope L) h q.2 hq.2).trans_lt hwindow

theorem eventually_integrableOn_atomicCuspSaddleMultiplier_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      IntegrableOn (fun q => logFlatSaddleProductIntegrand p.β 2 p.tStar
          (p.activeSaddleSlope L) (p.activeSaddleSlope L) h q *
        p.atomicCuspSaddleMultiplier L h s r q)
        (activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h)
        ((volume : Measure ℝ).prod volume) := by
  have hmodel := eventually_integrable_logFlatSaddleProduct (k := (2 : ℝ))
    hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L)
    (activeSaddleSlope_ne_zero hp L)
  filter_upwards [hmodel,
    eventually_continuousOn_atomicCuspSaddleMultiplier_of_radialData hp hRad hAcore hApot hL,
    eventually_norm_atomicCuspSaddleMultiplier_le_two_of_radialData hp hRad hAcore hApot hL]
    with h hi hc hb
  intro s r hs hr
  have hm := measurableSet_activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h
  apply hi.integrableOn.mul_bdd ((hc s r hs hr).aestronglyMeasurable hm)
  filter_upwards [ae_restrict_mem hm] with q hq
  exact hb s r hs hr q hq

/-- The error from the true multiplier tends to zero after the actual
product saddle normalization, uniformly in the two tangential parameters.
Integrability is a conclusion of the preceding theorem, not a new input. -/
theorem eventually_atomicCuspSaddleMultiplier_integral_error_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      let S := activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h
      let F := logFlatSaddleProductIntegrand p.β 2 p.tStar
        (p.activeSaddleSlope L) (p.activeSaddleSlope L) h
      ‖(logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h) ^ 2 *
        ((∫ q in S, F q * p.atomicCuspSaddleMultiplier L h s r q
          ∂(volume : Measure ℝ).prod volume) -
          ∫ q in S, F q ∂(volume : Measure ℝ).prod volume)‖ < ε := by
  let C := horizontalSaddleAbsoluteConstant p.β ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hscaled : C * δ < ε := by
    have hid : δ * (C + 1) = ε := div_mul_cancel₀ ε (by positivity : C + 1 ≠ 0)
    nlinarith
  have hmodel := eventually_logFlatSaddleProduct_multiplier_bound (k := (2 : ℝ))
    hp.β_pos (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L)
    (activeSaddleSlope_ne_zero hp L)
  filter_upwards [hmodel,
    eventually_integrableOn_atomicCuspSaddleMultiplier_of_radialData hp hRad hAcore hApot hL,
    eventually_atomicCuspSaddleMultiplier_uniform_of_radialData hp hRad hAcore hApot hL hδ]
    with h hb hi he
  intro s r hs hr
  have hm := measurableSet_activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h
  have herr : ∀ᵐ q ∂((volume : Measure ℝ).prod volume).restrict
      (activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h),
      ‖p.atomicCuspSaddleMultiplier L h s r q - 1‖ ≤ δ := by
    filter_upwards [ae_restrict_mem hm] with q hq
    exact (he s r hs hr q hq).le
  have hbound := hb _ (p.atomicCuspSaddleMultiplier L h s r) 1 δ hδ.le
    (hi s r hs hr) herr
  simp only [one_mul, ← pow_two] at hbound
  exact hbound.trans_lt hscaled

end CuspParameters
end InfiniteZero
