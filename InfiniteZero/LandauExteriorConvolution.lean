import InfiniteZero.HoppingSourceIdentity
import InfiniteZero.HoppingIntegrability
import InfiniteZero.LandauRadialL2
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The free Landau integral outside a compact source

The source support stays a positive distance from each exterior point.
The proved radial kernel bound and the unit modulus of its magnetic phase
therefore supply a local integrable majorant. This proves continuity and
upgrades almost-everywhere source representations to pointwise identities.
No resolvent-identification hypothesis is used in these analytic statements.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace InfiniteZero

theorem measurable_freeLandauKernel (b h E : ℝ) :
    Measurable (fun q : Plane × Plane => freeLandauKernel b h E q.1 q.2) := by
  unfold freeLandauKernel
  have hk := (measurable_landauKernel b h E).comp
    (show Measurable (fun q : Plane × Plane => ‖q.1 - q.2‖) by fun_prop)
  apply hk.complex_ofReal.mul
  unfold wedge
  fun_prop

/-- Joint continuity is asserted only away from the kernel diagonal. -/
theorem continuousAt_freeLandauKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) {q : Plane × Plane}
    (hq : 0 < ‖q.1 - q.2‖) :
    ContinuousAt (fun z : Plane × Plane => freeLandauKernel b h E z.1 z.2) q := by
  unfold freeLandauKernel
  have hn : ContinuousAt (fun z : Plane × Plane => ‖z.1 - z.2‖) q :=
    (continuousAt_fst.sub continuousAt_snd).norm
  have hk : ContinuousAt (fun z : Plane × Plane => landauKernel b h E ‖z.1 - z.2‖) q :=
    (continuousAt_landauKernel hb hh hE hq).comp
      (f := fun z : Plane × Plane => ‖z.1 - z.2‖) hn
  apply (Complex.continuous_ofReal.continuousAt.comp hk).mul
  unfold wedge
  fun_prop

theorem norm_freeLandauKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) {x y : Plane}
    (hxy : 0 < ‖x - y‖) :
    ‖freeLandauKernel b h E x y‖ = landauKernel b h E ‖x - y‖ := by
  simp only [freeLandauKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (landauKernel_pos hb hh hE hxy), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.ofReal_re,
    Complex.neg_im, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, neg_zero, Real.exp_zero, mul_one]

theorem norm_freeLandauKernel_le_of_separation {b h E δ : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hδ : 0 < δ) {x y : Plane}
    (hxy : δ ≤ ‖x - y‖) :
    ‖freeLandauKernel b h E x y‖ ≤ 1 / (Real.pi * E * δ ^ 2) := by
  have hd : 0 < ‖x - y‖ := hδ.trans_le hxy
  rw [norm_freeLandauKernel hb hh hE hd]
  apply (landauKernel_le hb hh hE hd).trans
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

private theorem source_integrable_of_support_subset_closedBall {F : Wavefunction} {a : ℝ}
    (hF : Continuous F) (hs : Function.support F ⊆ closedBall (0 : Plane) a) :
    Integrable F :=
  hF.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) a) hs)

private theorem source_norm_le_radius {F : Wavefunction} {a : ℝ}
    (hs : Function.support F ⊆ closedBall (0 : Plane) a) {y : Plane} (hy : F y ≠ 0) :
    ‖y‖ ≤ a := by
  simpa only [mem_closedBall, dist_zero_right] using hs hy

/-- Absolute convergence at every point exterior to the source ball. -/
theorem integrable_freeLandauKernel_mul_of_support_subset_closedBall
    {b h E a : ℝ} {F : Wavefunction}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hF : Continuous F)
    (hs : Function.support F ⊆ closedBall (0 : Plane) a)
    {x : Plane} (hx : a < ‖x‖) :
    Integrable (fun y : Plane => freeLandauKernel b h E x y * F y) := by
  have hδ : 0 < ‖x‖ - a := sub_pos.mpr hx
  have hi := (source_integrable_of_support_subset_closedBall hF hs).norm.const_mul
    (1 / (Real.pi * E * (‖x‖ - a) ^ 2))
  have hm : Measurable (fun y : Plane => freeLandauKernel b h E x y * F y) :=
    ((measurable_freeLandauKernel b h E).comp
      (measurable_const.prodMk measurable_id)).mul hF.measurable
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : F y = 0
  · simp only [hy, mul_zero, norm_zero]
    positivity
  have hsep : ‖x‖ - a ≤ ‖x - y‖ := by
    have hyn := source_norm_le_radius hs hy
    have hn := norm_sub_norm_le x y
    linarith
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_freeLandauKernel_le_of_separation hb hh hE hδ hsep) (norm_nonneg _)

/-- The convolution is continuous at each exterior point. The dominating
constant is local in that point, so no uniform separation is assumed globally. -/
theorem continuousAt_landauConvolution_exterior {b h E a : ℝ} {F : Wavefunction}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hF : Continuous F)
    (hs : Function.support F ⊆ closedBall (0 : Plane) a)
    {x : Plane} (hx : a < ‖x‖) :
    ContinuousAt (fun z : Plane => ∫ y : Plane, freeLandauKernel b h E z y * F y) x := by
  let δ := (‖x‖ - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hi := (source_integrable_of_support_subset_closedBall hF hs).norm.const_mul
    (1 / (Real.pi * E * δ ^ 2))
  refine continuousAt_of_dominated
    (bound := fun y : Plane => (1 / (Real.pi * E * δ ^ 2)) * ‖F y‖) ?_ ?_ hi ?_
  · exact Eventually.of_forall fun z =>
      (((measurable_freeLandauKernel b h E).comp
        (measurable_const.prodMk measurable_id)).mul hF.measurable).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x hδ] with z hz
    filter_upwards [] with y
    by_cases hy : F y = 0
    · simp only [hy, mul_zero, norm_zero]
      positivity
    have hyn := source_norm_le_radius hs hy
    have hnear : ‖x - z‖ < δ := by
      simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hz
    have hsep : δ ≤ ‖z - y‖ := by
      have h₁ := norm_sub_norm_le x z
      have h₂ := norm_sub_norm_le z y
      dsimp [δ] at hnear ⊢
      linarith
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_freeLandauKernel_le_of_separation hb hh hE hδ hsep) (norm_nonneg _)
  · filter_upwards [] with y
    by_cases hy : F y = 0
    · simp only [hy, mul_zero]
      exact continuousAt_const
    have hyn := source_norm_le_radius hs hy
    have hxy : 0 < ‖x - y‖ := by
      have hn := norm_sub_norm_le x y
      linarith
    have hk : ContinuousAt (fun z : Plane => freeLandauKernel b h E z y) x :=
      (continuousAt_freeLandauKernel hb hh hE (q := (x, y)) hxy).comp
        (f := fun z : Plane => (z, y)) (continuousAt_id.prodMk continuousAt_const)
    exact hk.mul continuousAt_const

theorem continuousOn_landauConvolution_exterior {b h E a : ℝ} {F : Wavefunction}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hF : Continuous F)
    (hs : Function.support F ⊆ closedBall (0 : Plane) a) :
    ContinuousOn (fun x : Plane => ∫ y : Plane, freeLandauKernel b h E x y * F y)
      {x : Plane | a < ‖x‖} :=
  fun _ hx => (continuousAt_landauConvolution_exterior hb hh hE hF hs hx).continuousWithinAt

/-- Almost-everywhere equality suffices on the open exterior because both
sides are continuous there and physical volume has full support. -/
theorem eqOn_landauConvolution_exterior_of_ae_eq {b h E a : ℝ} {F u : Wavefunction}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hF : Continuous F)
    (hs : Function.support F ⊆ closedBall (0 : Plane) a)
    (hu : ContinuousOn u {x : Plane | a < ‖x‖})
    (heq : ∀ᵐ x : Plane, u x = ∫ y : Plane, freeLandauKernel b h E x y * F y) :
    EqOn u (fun x : Plane => ∫ y : Plane, freeLandauKernel b h E x y * F y)
      {x : Plane | a < ‖x‖} := by
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae heq)
    (isOpen_lt continuous_const continuous_norm) hu
    (continuousOn_landauConvolution_exterior hb hh hE hF hs)

/-- The scalar prefactor in the unscaled resolvent convention is harmless. -/
theorem eqOn_const_mul_landauConvolution_exterior_of_ae_eq
    {b h E a : ℝ} {F u : Wavefunction} (c : ℂ)
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hF : Continuous F)
    (hs : Function.support F ⊆ closedBall (0 : Plane) a)
    (hu : ContinuousOn u {x : Plane | a < ‖x‖})
    (heq : ∀ᵐ x : Plane, u x = c * ∫ y : Plane, freeLandauKernel b h E x y * F y) :
    EqOn u (fun x : Plane => c * ∫ y : Plane, freeLandauKernel b h E x y * F y)
      {x : Plane | a < ‖x‖} := by
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae heq)
    (isOpen_lt continuous_const continuous_norm) hu
    (continuousOn_const.mul (continuousOn_landauConvolution_exterior hb hh hE hF hs))

end InfiniteZero
