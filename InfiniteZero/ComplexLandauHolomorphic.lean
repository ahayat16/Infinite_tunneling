import InfiniteZero.ComplexLandauKernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville

/-!
# Holomorphy of the actual complex radial Landau kernel

On a neighborhood of each permitted radius, the defining integrand is bounded
by one fixed integrable real Landau integrand. Cauchy's estimate gives the
corresponding integrable derivative bound on a smaller neighborhood, so
differentiation under the proper-time integral is justified.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace InfiniteZero

def complexLandauRadiusDomain : Set ℂ := {r | 0 < (r ^ 2).re}

theorem isOpen_complexLandauRadiusDomain : IsOpen complexLandauRadiusDomain := by
  exact isOpen_lt continuous_const (by fun_prop)

theorem differentiable_complexLandauIntegrand_radius (b h E τ : ℝ) :
    Differentiable ℂ (fun r => complexLandauIntegrand b h E r τ) := by
  unfold complexLandauIntegrand
  fun_prop

/-- Explicit radial derivative; all dependence on proper time is measurable. -/
theorem hasDerivAt_complexLandauIntegrand_radius (b h E τ : ℝ) (r : ℂ) :
    HasDerivAt (fun z => complexLandauIntegrand b h E z τ)
      ((-(b : ℂ) / (2 * (h : ℂ)) * r *
        ((Real.cosh (b * τ) / Real.sinh (b * τ) : ℝ) : ℂ)) *
          complexLandauIntegrand b h E r τ) r := by
  have hp := (((((hasDerivAt_id r).pow 2).const_mul ((b / 4 : ℝ) : ℂ)).mul_const
    ((Real.cosh (b * τ) / Real.sinh (b * τ) : ℝ) : ℂ)).const_add ((E * τ : ℝ) : ℂ)).neg
  have hd := ((hp.div_const (h : ℂ)).cexp).const_mul (((Real.sinh (b * τ) : ℝ) : ℂ)⁻¹)
  convert hd using 1
  unfold complexLandauIntegrand
  simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one]
  push_cast
  ring

theorem measurable_deriv_complexLandauIntegrand_radius (b h E : ℝ) (r : ℂ) :
    Measurable (fun τ : ℝ => deriv (fun z => complexLandauIntegrand b h E z τ) r) := by
  simp_rw [(hasDerivAt_complexLandauIntegrand_radius b h E _ r).deriv]
  unfold complexLandauIntegrand
  fun_prop

/-- A fixed real radius controls every complex radius whose squared real part
has the indicated positive lower bound. -/
theorem norm_complexLandauIntegrand_le_of_re_sq {b h a τ : ℝ} {r : ℂ}
    (hb : 0 < b) (hh : 0 < h) (ha : 0 < a) (hτ : 0 < τ)
    (hr : a ≤ (r ^ 2).re) (E : ℝ) :
    ‖complexLandauIntegrand b h E r τ‖ ≤ landauIntegrand b h E (Real.sqrt a) τ := by
  rw [norm_complexLandauIntegrand hb hτ h E (ha.le.trans hr)]
  unfold landauIntegrand
  apply mul_le_mul_of_nonneg_left _ (by
    exact (inv_pos.mpr (Real.sinh_pos_iff.mpr (mul_pos hb hτ))).le)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hh.le
  apply neg_le_neg
  unfold properTimePhase complexLandauEffectiveRadius
  rw [Real.sq_sqrt ha.le, Real.sq_sqrt (ha.le.trans hr)]
  gcongr

/-- The local majorant is derived from continuity of `Re(r²)`. -/
theorem exists_complexLandauIntegrand_local_majorant {b h E : ℝ} {r₀ : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hr₀ : 0 < (r₀ ^ 2).re) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r ∈ ball r₀ ρ, ∀ τ > 0,
      ‖complexLandauIntegrand b h E r τ‖ ≤
        landauIntegrand b h E (Real.sqrt ((r₀ ^ 2).re / 2)) τ := by
  have hc : Continuous (fun r : ℂ => (r ^ 2).re) := by fun_prop
  have he : ∀ᶠ r : ℂ in 𝓝 r₀, (r₀ ^ 2).re / 2 < (r ^ 2).re :=
    (hc.tendsto r₀).eventually (lt_mem_nhds (by linarith))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨ρ, hρ, fun r hr τ hτ =>
    norm_complexLandauIntegrand_le_of_re_sq hb hh (half_pos hr₀) hτ (hball hr).le E⟩

theorem differentiableAt_complexLandauKernel {b h E : ℝ} {r₀ : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr₀ : 0 < (r₀ ^ 2).re) :
    DifferentiableAt ℂ (complexLandauKernel b h E) r₀ := by
  obtain ⟨ρ, hρ, hmajor⟩ := exists_complexLandauIntegrand_local_majorant (E := E) hb hh hr₀
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F := fun r : ℂ => complexLandauIntegrand b h E r
  let F' := fun r τ => deriv (fun z => F z τ) r
  let B := fun τ => landauIntegrand b h E (Real.sqrt ((r₀ ^ 2).re / 2)) τ / (ρ / 2)
  have hB : Integrable B μ :=
    (integrableOn_landauIntegrand hb hh hE (Real.sqrt_pos.mpr (half_pos hr₀))).div_const (ρ / 2)
  have hderiv : ∀ᵐ τ ∂μ, ∀ r ∈ ball r₀ (ρ / 2), ‖F' r τ‖ ≤ B τ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    intro r hr
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hρ)
      (differentiable_complexLandauIntegrand_radius b h E τ).diffContOnCl
    intro z hz
    apply hmajor z _ τ hτ
    have hzr : dist z r = ρ / 2 := hz
    have hrr : dist r r₀ < ρ / 2 := hr
    exact (dist_triangle z r r₀).trans_lt (by linarith)
  have hdiff : ∀ᵐ τ ∂μ, ∀ r ∈ ball r₀ (ρ / 2), HasDerivAt (fun z => F z τ) (F' r τ) r :=
    Eventually.of_forall fun τ r _ =>
      (differentiable_complexLandauIntegrand_radius b h E τ r).hasDerivAt
  have hmeas : ∀ᶠ r in 𝓝 r₀, AEStronglyMeasurable (F r) μ :=
    Eventually.of_forall fun r =>
      (continuousOn_complexLandauIntegrand hb h E r).aestronglyMeasurable measurableSet_Ioi
  have hmeas' : AEStronglyMeasurable (F' r₀) μ :=
    (measurable_deriv_complexLandauIntegrand_radius b h E r₀).aestronglyMeasurable
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (Metric.ball_mem_nhds r₀ (half_pos hρ)) hmeas
    (integrableOn_complexLandauIntegrand hb hh hE hr₀) hmeas' hderiv hB hdiff
  exact hint.2.differentiableAt.const_mul ((b / (4 * Real.pi * h ^ 2) : ℝ) : ℂ)

theorem differentiableOn_complexLandauKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) :
    DifferentiableOn ℂ (complexLandauKernel b h E) complexLandauRadiusDomain :=
  fun _ hr => (differentiableAt_complexLandauKernel hb hh hE hr).differentiableWithinAt

theorem analyticOnNhd_complexLandauKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) :
    AnalyticOnNhd ℂ (complexLandauKernel b h E) complexLandauRadiusDomain :=
  (differentiableOn_complexLandauKernel hb hh hE).analyticOnNhd isOpen_complexLandauRadiusDomain

end InfiniteZero
