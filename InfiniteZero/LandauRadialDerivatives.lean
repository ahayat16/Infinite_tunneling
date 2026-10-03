import InfiniteZero.ComplexLandauHolomorphic
import InfiniteZero.LandauIntegrandODE
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Differentiating the real Landau kernel in the radius

Two Cauchy estimates turn the local proper-time majorant for the complex
kernel into integrable majorants for its first two radial derivatives.
Differentiation under the real proper-time integral then gives the explicit
first and second radial derivatives of the original real kernel.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace InfiniteZero

private theorem differentiable_deriv_complexLandauIntegrand_radius (b h E τ : ℝ) :
    Differentiable ℂ (fun r => deriv (fun z => complexLandauIntegrand b h E z τ) r) := by
  simp_rw [(hasDerivAt_complexLandauIntegrand_radius b h E τ _).deriv]
  unfold complexLandauIntegrand
  fun_prop

private theorem exists_complexLandau_radial_derivative_majorants
    {b h E : ℝ} {r : ℂ} (hb : 0 < b) (hh : 0 < h) (hE : 0 < E)
    (hr : 0 < (r ^ 2).re) :
    ∃ ε > 0, ∃ B₁ B₂ : ℝ → ℝ,
      IntegrableOn B₁ (Ioi 0) ∧ IntegrableOn B₂ (Ioi 0) ∧
      ∀ z ∈ ball r ε, ∀ τ > 0,
        ‖deriv (fun w => complexLandauIntegrand b h E w τ) z‖ ≤ B₁ τ ∧
        ‖deriv (fun w => deriv (fun v => complexLandauIntegrand b h E v τ) w) z‖ ≤
          B₂ τ := by
  obtain ⟨ρ, hρ, hmajor⟩ := exists_complexLandauIntegrand_local_majorant (E := E) hb hh hr
  let B₀ := landauIntegrand b h E (Real.sqrt ((r ^ 2).re / 2))
  let B₁ := fun τ => B₀ τ / (ρ / 2)
  let B₂ := fun τ => B₁ τ / (ρ / 4)
  have hB₀ : IntegrableOn B₀ (Ioi 0) :=
    integrableOn_landauIntegrand hb hh hE (Real.sqrt_pos.mpr (half_pos hr))
  have hfirst : ∀ z ∈ ball r (ρ / 2), ∀ τ > 0,
      ‖deriv (fun w => complexLandauIntegrand b h E w τ) z‖ ≤ B₁ τ := by
    intro z hz τ hτ
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hρ)
      (differentiable_complexLandauIntegrand_radius b h E τ).diffContOnCl
    intro w hw
    apply hmajor w _ τ hτ
    have hwz : dist w z = ρ / 2 := hw
    have hzr : dist z r < ρ / 2 := hz
    exact (dist_triangle w z r).trans_lt (by linarith)
  refine ⟨ρ / 4, by positivity, B₁, B₂, hB₀.div_const _,
    (hB₀.div_const _).div_const _, ?_⟩
  intro z hz τ hτ
  have hzr : dist z r < ρ / 4 := hz
  refine ⟨hfirst z (by change dist z r < ρ / 2; linarith) τ hτ, ?_⟩
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < ρ / 4)
    (differentiable_deriv_complexLandauIntegrand_radius b h E τ).diffContOnCl
  intro w hw
  apply hfirst w _ τ hτ
  have hwz : dist w z = ρ / 4 := hw
  exact (dist_triangle w z r).trans_lt (by linarith)

private theorem re_deriv_complexLandauIntegrand (b h E τ r : ℝ) :
    (deriv (fun z => complexLandauIntegrand b h E z τ) (r : ℂ)).re =
      landauIntegrandRadialDeriv b h E r τ := by
  have hd := (differentiable_complexLandauIntegrand_radius b h E τ (r : ℂ)).hasDerivAt
  have hreal : HasDerivAt (fun x : ℝ => landauIntegrand b h E x τ)
      (deriv (fun z => complexLandauIntegrand b h E z τ) (r : ℂ)).re r := by
    simpa only [complexLandauIntegrand_ofReal, Complex.ofReal_re] using hd.real_of_complex
  exact hreal.unique (hasDerivAt_landauIntegrand_radius b h E τ r)

private theorem re_second_deriv_complexLandauIntegrand (b h E τ r : ℝ) :
    (deriv (fun z => deriv (fun w => complexLandauIntegrand b h E w τ) z) (r : ℂ)).re =
      landauIntegrandRadialSecond b h E r τ := by
  have hd := (differentiable_deriv_complexLandauIntegrand_radius b h E τ (r : ℂ)).hasDerivAt
  have hreal : HasDerivAt (fun x : ℝ => landauIntegrandRadialDeriv b h E x τ)
      (deriv (fun z => deriv (fun w => complexLandauIntegrand b h E w τ) z) (r : ℂ)).re r := by
    simpa only [re_deriv_complexLandauIntegrand] using hd.real_of_complex
  exact hreal.unique (hasDerivAt_landauIntegrandRadialDeriv_radius b h E τ r)

private theorem exists_landau_radial_derivative_majorants {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    ∃ ε > 0, ∃ B₁ B₂ : ℝ → ℝ,
      IntegrableOn B₁ (Ioi 0) ∧ IntegrableOn B₂ (Ioi 0) ∧
      ∀ x ∈ ball r ε, ∀ τ > 0,
        ‖landauIntegrandRadialDeriv b h E x τ‖ ≤ B₁ τ ∧
        ‖landauIntegrandRadialSecond b h E x τ‖ ≤ B₂ τ := by
  have hr' : 0 < (((r : ℂ) ^ 2).re) := by
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos hr
  obtain ⟨ε, hε, B₁, B₂, hB₁, hB₂, hmajor⟩ :=
    exists_complexLandau_radial_derivative_majorants hb hh hE hr'
  refine ⟨ε, hε, B₁, B₂, hB₁, hB₂, ?_⟩
  intro x hx τ hτ
  have hx' : (x : ℂ) ∈ ball (r : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hx
  have hm := hmajor (x : ℂ) hx' τ hτ
  constructor
  · rw [Real.norm_eq_abs, ← re_deriv_complexLandauIntegrand]
    exact (Complex.abs_re_le_norm _).trans hm.1
  · rw [Real.norm_eq_abs, ← re_second_deriv_complexLandauIntegrand]
    exact (Complex.abs_re_le_norm _).trans hm.2

private theorem measurable_landauIntegrandRadialDeriv (b h E r : ℝ) :
    Measurable (landauIntegrandRadialDeriv b h E r) := by
  unfold landauIntegrandRadialDeriv landauRadialSlope landauIntegrand properTimePhase
  fun_prop

private theorem measurable_landauIntegrandRadialSecond (b h E r : ℝ) :
    Measurable (landauIntegrandRadialSecond b h E r) := by
  unfold landauIntegrandRadialSecond landauRadialSlope landauIntegrand properTimePhase
  fun_prop

private theorem integral_landauIntegrand_hasDerivAt {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    IntegrableOn (landauIntegrandRadialDeriv b h E r) (Ioi 0) ∧
      HasDerivAt (fun x => ∫ τ in Ioi (0 : ℝ), landauIntegrand b h E x τ)
        (∫ τ in Ioi (0 : ℝ), landauIntegrandRadialDeriv b h E r τ) r := by
  obtain ⟨ε, hε, B₁, _, hB₁, _, hmajor⟩ :=
    exists_landau_radial_derivative_majorants hb hh hE hr
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (Metric.ball_mem_nhds r hε)
    (Eventually.of_forall fun x => (continuousOn_landauIntegrand hb h E x).aestronglyMeasurable
      measurableSet_Ioi)
    (integrableOn_landauIntegrand hb hh hE hr)
    (measurable_landauIntegrandRadialDeriv b h E r).aestronglyMeasurable _ hB₁
  · exact Eventually.of_forall fun τ x _ => hasDerivAt_landauIntegrand_radius b h E τ x
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact fun x hx => (hmajor x hx τ hτ).1

/-- The explicit first radial derivative of the integrand is integrable. -/
theorem integrableOn_landauIntegrandRadialDeriv {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    IntegrableOn (landauIntegrandRadialDeriv b h E r) (Ioi 0) :=
  (integral_landauIntegrand_hasDerivAt hb hh hE hr).1

private theorem integral_landauIntegrandRadialDeriv_hasDerivAt {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    IntegrableOn (landauIntegrandRadialSecond b h E r) (Ioi 0) ∧
      HasDerivAt (fun x => ∫ τ in Ioi (0 : ℝ), landauIntegrandRadialDeriv b h E x τ)
        (∫ τ in Ioi (0 : ℝ), landauIntegrandRadialSecond b h E r τ) r := by
  obtain ⟨ε, hε, _, B₂, _, hB₂, hmajor⟩ :=
    exists_landau_radial_derivative_majorants hb hh hE hr
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (Metric.ball_mem_nhds r hε)
    (Eventually.of_forall fun x => (measurable_landauIntegrandRadialDeriv b h E x).aestronglyMeasurable)
    (integrableOn_landauIntegrandRadialDeriv hb hh hE hr)
    (measurable_landauIntegrandRadialSecond b h E r).aestronglyMeasurable _ hB₂
  · exact Eventually.of_forall fun τ x _ => hasDerivAt_landauIntegrandRadialDeriv_radius b h E τ x
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact fun x hx => (hmajor x hx τ hτ).2

/-- The explicit second radial derivative of the integrand is integrable. -/
theorem integrableOn_landauIntegrandRadialSecond {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    IntegrableOn (landauIntegrandRadialSecond b h E r) (Ioi 0) :=
  (integral_landauIntegrandRadialDeriv_hasDerivAt hb hh hE hr).1

/-- First differentiation under the defining proper-time integral. -/
theorem hasDerivAt_landauKernel {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    HasDerivAt (landauKernel b h E)
      (b / (4 * Real.pi * h ^ 2) *
        ∫ τ in Ioi (0 : ℝ), landauIntegrandRadialDeriv b h E r τ) r :=
  (integral_landauIntegrand_hasDerivAt hb hh hE hr).2.const_mul _

theorem deriv_landauKernel {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    deriv (landauKernel b h E) r = b / (4 * Real.pi * h ^ 2) *
      ∫ τ in Ioi (0 : ℝ), landauIntegrandRadialDeriv b h E r τ :=
  (hasDerivAt_landauKernel hb hh hE hr).deriv

/-- Second differentiation under the defining proper-time integral. -/
theorem hasDerivAt_deriv_landauKernel {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    HasDerivAt (deriv (landauKernel b h E))
      (b / (4 * Real.pi * h ^ 2) *
        ∫ τ in Ioi (0 : ℝ), landauIntegrandRadialSecond b h E r τ) r := by
  apply ((integral_landauIntegrandRadialDeriv_hasDerivAt hb hh hE hr).2.const_mul
    (b / (4 * Real.pi * h ^ 2))).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with x hx
  exact deriv_landauKernel hb hh hE hx

theorem deriv_deriv_landauKernel {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) :
    deriv (deriv (landauKernel b h E)) r = b / (4 * Real.pi * h ^ 2) *
      ∫ τ in Ioi (0 : ℝ), landauIntegrandRadialSecond b h E r τ :=
  (hasDerivAt_deriv_landauKernel hb hh hE hr).deriv

end InfiniteZero
