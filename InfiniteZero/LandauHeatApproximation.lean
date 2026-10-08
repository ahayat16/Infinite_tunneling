import InfiniteZero.LandauHeatKernel
import InfiniteZero.PlaneGaussianIntegral
import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# The initial value of the explicit magnetic Gaussian

The normalized scalar Gaussian is an approximation of the identity. For a
fixed observation point the magnetic phase is a continuous multiplier,
independent of time, and equals one on the diagonal.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InfiniteZero

/-- The planar normalized Gaussian converges to point evaluation. -/
theorem tendsto_planeGaussian_average {g : Plane → ℂ} (hg : Integrable g)
    {x : Plane} (hgc : ContinuousAt g x) :
    Tendsto (fun a : ℝ => ∫ y : Plane,
      (a / Real.pi * Real.exp (-a * ‖x - y‖ ^ 2)) • g y)
      atTop (𝓝 (g x)) := by
  let p : Plane → ℝ := fun z => Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2)
  have hp0 : ∀ z, 0 ≤ p z := by intro z; dsimp [p]; positivity
  have hpi : (∫ z : Plane, p z) = 1 := by
    rw [show p = fun z => Real.pi⁻¹ * Real.exp (-(1 : ℝ) * ‖z‖ ^ 2) by
      funext z; simp [p], integral_const_mul, integral_planeGaussian (by norm_num)]
    simp [Real.pi_ne_zero]
  have hpd : Tendsto (fun z : Plane => ‖z‖ ^ Module.finrank ℝ Plane * p z)
      (Bornology.cobounded Plane) (𝓝 0) := by
    have hn : Tendsto (fun z : Plane => ‖z‖ ^ 2)
        (Bornology.cobounded Plane) atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cobounded_atTop
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hn).const_mul Real.pi⁻¹
    simpa [p, Plane, mul_assoc, mul_comm, mul_left_comm] using h
  have h := tendsto_integral_comp_smul_smul_of_integrable' hp0 hpi hpd hg hgc
  have h' := h.comp Real.tendsto_sqrt_atTop
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  simp only [p, Plane, finrank_euclideanSpace, Fintype.card_fin, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a), mul_pow, Real.sq_sqrt ha]
  ring

/-- The magnetic Gaussian rate diverges at positive time zero. -/
theorem landauHeatRate_tendsto_atTop {B : ℝ} (hB : 0 < B) :
    Tendsto (landauHeatRate B) (𝓝[>] (0 : ℝ)) atTop := by
  have ht : Tendsto (fun t : ℝ => B * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((continuous_const.mul continuous_id : Continuous (fun t : ℝ => B * t)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun t : ℝ => Real.sinh (B * t)) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using Real.continuous_sinh.continuousAt.tendsto.comp ht
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sinh_pos_iff.mpr (mul_pos hB ht)
  have hc : Tendsto (fun t : ℝ => B / 4 * Real.cosh (B * t))
      (𝓝[>] (0 : ℝ)) (𝓝 (B / 4)) := by
    simpa using (Real.continuous_cosh.continuousAt.tendsto.comp ht).const_mul (B / 4)
  change Tendsto (fun t => landauHeatRate B t) _ _
  simpa only [landauHeatRate, div_eq_mul_inv, mul_assoc] using
    hc.pos_mul_atTop (by positivity) (tendsto_inv_nhdsGT_zero.comp hs)

/-- Scalar normalization of the magnetic Gaussian. -/
theorem landauHeatAmplitude_eq_rate_div (B t : ℝ) :
    landauHeatAmplitude B t = (Real.cosh (B * t))⁻¹ *
      (landauHeatRate B t / Real.pi) := by
  unfold landauHeatAmplitude landauHeatRate
  field_simp [(Real.cosh_pos (B * t)).ne']


/-- The explicit magnetic heat kernel recovers every smooth compactly
supported source as time decreases to zero. -/
theorem landauHeatAction_tendsto_zero {B : ℝ} (hB : 0 < B)
    {f : Wavefunction} (hf : IsTestFunction f) (x : Plane) :
    Tendsto (fun t : ℝ => landauHeatAction B t f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  let g : Plane → ℂ := fun y =>
    Complex.exp (-Complex.I * ((B / 2 * wedge x y : ℝ) : ℂ)) * f y
  have hgc : Continuous g := by
    dsimp [g, wedge, mul_comm]
    apply Continuous.mul ?_ hf.1.continuous
    fun_prop
  have hgi : Integrable g :=
    hgc.integrable_of_hasCompactSupport (hf.2.mul_left)
  have hgx : g x = f x := by
    simp [g, wedge, mul_comm]
  have hga := (tendsto_planeGaussian_average (x := x) hgi hgc.continuousAt).comp
    (landauHeatRate_tendsto_atTop hB)
  have ht : Tendsto (fun t : ℝ => (Real.cosh (B * t))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : Continuous (fun t : ℝ => (Real.cosh (B * t))⁻¹) :=
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
        (fun t => (Real.cosh_pos (B * t)).ne')
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := ht.smul hga
  simp only [one_smul, hgx] at h
  convert h using 1
  ext t
  dsimp only [Function.comp_apply, landauHeatAction]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [landauHeatKernel, g,
    landauHeatAmplitude_eq_rate_div, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_div, mul_assoc]

end InfiniteZero
