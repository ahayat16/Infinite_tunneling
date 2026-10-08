import InfiniteZero.LogFlatContourMultiplier
import InfiniteZero.CuspKernelProfileHolomorphic
import InfiniteZero.LogFlatActiveTruncation

/-!
# Exact fiberwise contour shifts of the physical incoming multiplier

The core/full energies and frozen profile are the actual atomic ones.
Holomorphy and boundedness on the logarithmic half-strip are consequences
of the common geometric bidisc and the proved uniform profile bound.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval

namespace InfiniteZero

theorem norm_logarithmicPoint_le_activeWindow_of_re {tStar h : ℝ}
    (htStar : 0 < tStar) {z : ℂ} (hz : logFlatActiveLogCut h ≤ z.re) :
    ‖(tStar : ℂ) * Complex.exp (-z)‖ ≤ logFlatActiveWindow tStar h := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htStar,
    Complex.norm_exp, Complex.neg_re]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hz)) htStar.le

namespace CuspParameters

/-- The physical normalized profile as a function of the first logarithmic
normal variable, with the second complex normal coordinate held fixed. -/
def atomicCuspLogMultiplier (p : CuspParameters) (L h s r : ℝ) (u z : ℂ) : ℂ :=
  p.frozenCuspKernelPhaseProfile L h
    (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹) s r
    ((p.tStar : ℂ) * Complex.exp (-z)) u

/-- The corresponding fiber in the second logarithmic normal variable. -/
def atomicCuspLogMultiplierSecond (p : CuspParameters) (L h s r : ℝ) (t z : ℂ) : ℂ :=
  p.frozenCuspKernelPhaseProfile L h
    (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹) s r
    t ((p.tStar : ℂ) * Complex.exp (-z))

/-- The entire logarithmic half-plane maps into the shrinking normal
window, independently of the vertical shift and of its sign. -/
theorem eventually_atomicCuspLogMultiplier_properties_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ u : ℂ, ‖u‖ ≤ logFlatActiveWindow p.tStar h → ∀ v : ℝ,
        DifferentiableOn ℂ (p.atomicCuspLogMultiplier L h s r u)
          (logFlatContourHalfStrip (logFlatActiveLogCut h) v) ∧
        (∀ z ∈ logFlatContourHalfStrip (logFlatActiveLogCut h) v,
          ‖p.atomicCuspLogMultiplier L h s r u z‖ ≤ 2) ∧
        DifferentiableOn ℂ (p.atomicCuspLogMultiplierSecond L h s r u)
          (logFlatContourHalfStrip (logFlatActiveLogCut h) v) ∧
        (∀ z ∈ logFlatContourHalfStrip (logFlatActiveLogCut h) v,
          ‖p.atomicCuspLogMultiplierSecond L h s r u z‖ ≤ 2) := by
  obtain ⟨η, hη, hhol⟩ := exists_uniform_frozenCuspKernelPhaseProfile_bidisc hp hL
  obtain ⟨T, _hT, henergies⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  have hw := (tendsto_logFlatActiveWindow p.tStar).eventually (gt_mem_nhds hη)
  have hb := eventually_norm_atomic_frozenCuspKernelPhaseProfile_le_two_of_radialData
    hp hRad hAcore hApot hL (by norm_num : (0 : ℝ) ≤ 1)
  filter_upwards [hw, hb, tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T),
    self_mem_nhdsWithin] with h hwindow hbound hT hh
  intro s r hs hr u hu v
  have hE := henergies h⁻¹ hT
  simp only [inv_inv] at hE
  have hEc : 0 < -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹) := by
    linarith [hE.2.1.1]
  have hEf : 0 < scaledAtomicEnergy p h⁻¹ := by linarith [hE.1.1]
  have ha := (hhol s r hs hr h hh _ hEc _ hEf).differentiableOn
  have hn : ∀ z ∈ logFlatContourHalfStrip (logFlatActiveLogCut h) v,
      ‖(p.tStar : ℂ) * Complex.exp (-z)‖ ≤ logFlatActiveWindow p.tStar h :=
    fun z hz => norm_logarithmicPoint_le_activeWindow_of_re (hp.t₀_pos.trans hp.t₀_lt) hz.1
  have hd : Differentiable ℂ (fun z : ℂ => (p.tStar : ℂ) * Complex.exp (-z)) := by
    fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmap : MapsTo (fun z : ℂ => ((p.tStar : ℂ) * Complex.exp (-z), u))
        (logFlatContourHalfStrip (logFlatActiveLogCut h) v)
        (Metric.ball (0 : ℂ) η ×ˢ Metric.ball (0 : ℂ) η) := fun z hz =>
      ⟨by simpa only [Metric.mem_ball, dist_zero_right] using (hn z hz).trans_lt hwindow,
       by simpa only [Metric.mem_ball, dist_zero_right] using hu.trans_lt hwindow⟩
    simpa only [atomicCuspLogMultiplier, Function.comp_apply] using
      ha.comp (hd.prodMk (differentiable_const u)).differentiableOn hmap
  · intro z hz
    simpa only [atomicCuspLogMultiplier, one_mul] using
      hbound s r hs hr ((p.tStar : ℂ) * Complex.exp (-z)) u
        (by simpa only [one_mul] using hn z hz) (by simpa only [one_mul] using hu)
  · have hmap : MapsTo (fun z : ℂ => (u, (p.tStar : ℂ) * Complex.exp (-z)))
        (logFlatContourHalfStrip (logFlatActiveLogCut h) v)
        (Metric.ball (0 : ℂ) η ×ˢ Metric.ball (0 : ℂ) η) := fun z hz =>
      ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu.trans_lt hwindow,
       by simpa only [Metric.mem_ball, dist_zero_right] using (hn z hz).trans_lt hwindow⟩
    simpa only [atomicCuspLogMultiplierSecond, Function.comp_apply] using
      ha.comp ((differentiable_const u).prodMk hd).differentiableOn hmap
  · intro z hz
    simpa only [atomicCuspLogMultiplierSecond, one_mul] using
      hbound s r hs hr u ((p.tStar : ℂ) * Complex.exp (-z))
        (by simpa only [one_mul] using hu) (by simpa only [one_mul] using hn z hz)

/-- Exact first-normal contour shift for the actual physical profile.
The threshold precedes both tangential coordinates, the fixed second normal
coordinate, and the vertical shift. Taking `v` to be the imaginary part of
the complex critical point gives the saddle ray used in the incoming cell. -/
theorem eventually_atomicCuspLogMultiplier_ray_shift_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ u : ℂ, ‖u‖ ≤ logFlatActiveWindow p.tStar h → ∀ v : ℝ,
        let a := logFlatActiveLogCut h
        let F := fun z : ℂ => logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h z *
          p.atomicCuspLogMultiplier L h s r u z
        (∀ η ∈ uIcc 0 v,
          IntegrableOn (fun x : ℝ => F ((x : ℂ) + (η : ℂ) * Complex.I)) (Ioi a)) ∧
        IntervalIntegrable (fun η : ℝ => F ((a : ℂ) + (η : ℂ) * Complex.I)) volume 0 v ∧
        (∫ x in Ioi a, F (x : ℂ)) =
          Complex.I * (∫ η in 0..v, F ((a : ℂ) + (η : ℂ) * Complex.I)) +
          (∫ x in Ioi a, F ((x : ℂ) + (v : ℂ) * Complex.I)) := by
  filter_upwards [eventually_atomicCuspLogMultiplier_properties_of_radialData
    hp hRad hAcore hApot hL] with h hprop
  intro s r hs hr u hu v
  obtain ⟨hB, hbound, _hBsecond, _hboundSecond⟩ := hprop s r hs hr u hu v
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro η hη
    simpa only [logFlatContourFunction, logFlatComplexMultiplierIntegrand,
      logFlatComplexIntegrand] using
      integrableOn_logFlatComplexMultiplierIntegrand_ray hp.β_pos 2
        (p.activeSaddleSlope L * (p.tStar : ℂ) / (h : ℂ)) hB hbound hη
  · simpa only [logFlatContourFunction, logFlatComplexMultiplierIntegrand,
      logFlatComplexIntegrand] using
      intervalIntegrable_logFlatComplexMultiplierIntegrand_vertical p.β 2
        (p.activeSaddleSlope L * (p.tStar : ℂ) / (h : ℂ)) hB le_rfl
  · simpa only [logFlatContourFunction, logFlatComplexMultiplierIntegrand,
      logFlatComplexIntegrand] using
      logFlatComplex_multiplier_ray_shift hp.β_pos 2
        (p.activeSaddleSlope L * (p.tStar : ℂ) / (h : ℂ)) (logFlatActiveLogCut h) v
        hB (by norm_num : (0 : ℝ) ≤ 2) hbound

/-- Exact second-normal contour shift, uniformly in the first complex
normal coordinate. This is the other fiber required for the product contour. -/
theorem eventually_atomicCuspLogMultiplierSecond_ray_shift_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ t : ℂ, ‖t‖ ≤ logFlatActiveWindow p.tStar h → ∀ v : ℝ,
        let a := logFlatActiveLogCut h
        let F := fun z : ℂ => logFlatContourFunction p.β 2 p.tStar (p.activeSaddleSlope L) h z *
          p.atomicCuspLogMultiplierSecond L h s r t z
        (∀ η ∈ uIcc 0 v,
          IntegrableOn (fun x : ℝ => F ((x : ℂ) + (η : ℂ) * Complex.I)) (Ioi a)) ∧
        IntervalIntegrable (fun η : ℝ => F ((a : ℂ) + (η : ℂ) * Complex.I)) volume 0 v ∧
        (∫ x in Ioi a, F (x : ℂ)) =
          Complex.I * (∫ η in 0..v, F ((a : ℂ) + (η : ℂ) * Complex.I)) +
          (∫ x in Ioi a, F ((x : ℂ) + (v : ℂ) * Complex.I)) := by
  filter_upwards [eventually_atomicCuspLogMultiplier_properties_of_radialData
    hp hRad hAcore hApot hL] with h hprop
  intro s r hs hr t ht v
  obtain ⟨_hBfirst, _hboundFirst, hB, hbound⟩ := hprop s r hs hr t ht v
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro η hη
    simpa only [logFlatContourFunction, logFlatComplexMultiplierIntegrand,
      logFlatComplexIntegrand] using
      integrableOn_logFlatComplexMultiplierIntegrand_ray hp.β_pos 2
        (p.activeSaddleSlope L * (p.tStar : ℂ) / (h : ℂ)) hB hbound hη
  · simpa only [logFlatContourFunction, logFlatComplexMultiplierIntegrand,
      logFlatComplexIntegrand] using
      intervalIntegrable_logFlatComplexMultiplierIntegrand_vertical p.β 2
        (p.activeSaddleSlope L * (p.tStar : ℂ) / (h : ℂ)) hB le_rfl
  · simpa only [logFlatContourFunction, logFlatComplexMultiplierIntegrand,
      logFlatComplexIntegrand] using
      logFlatComplex_multiplier_ray_shift hp.β_pos 2
        (p.activeSaddleSlope L * (p.tStar : ℂ) / (h : ℂ)) (logFlatActiveLogCut h) v
        hB (by norm_num : (0 : ℝ) ≤ 2) hbound

end CuspParameters
end InfiniteZero
