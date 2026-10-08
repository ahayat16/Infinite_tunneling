import InfiniteZero.ComplexLandauHolomorphic
import InfiniteZero.ComplexLandauSmallDisk
import InfiniteZero.LandauKernelExactActionUpper
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exact-action bounds for every radial Landau derivative

Cauchy's estimate on a complex disk of radius `h` costs precisely one power
of `h⁻¹` per derivative. The effective real radius varies by `O(h)`, so the
full action at the center is retained. The constants and semiclassical
threshold are independent of the derivative order, with an explicit factorial.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace InfiniteZero

/-- The full real action at the center controls the complex kernel on a
closed disk of radius `h`. All constants precede the energy and radius. -/
theorem exists_uniform_complexLandauKernel_disk_bound
    {b Emin Emax rMin rMax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin)
    (hEmax : Emin ≤ Emax) (hMin : 0 < rMin) (hMax : rMin ≤ rMax) :
    ∃ C > 0, ∃ h₀ > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rMin rMax,
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z ∈ closedBall (r : ℂ) h,
        0 < (z ^ 2).re ∧ ‖complexLandauKernel b h E z‖ ≤
          C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction b E r / h) := by
  obtain ⟨h₀, hh₀, A, hA, hDisk⟩ :=
    exists_complexLandau_smallDisk_action_bounds (Emax := Emax) (rMax := rMax)
      hb hEmin hMin
  obtain ⟨C, hC, hKernel⟩ := exists_uniform_landauKernel_exact_action_upper
    hb hEmin hEmax (half_pos hMin) (show rMin / 2 ≤ rMax + 1 by linarith)
  refine ⟨C * Real.exp A, by positivity, min h₀ 1, lt_min hh₀ zero_lt_one, ?_⟩
  intro E hE r hr h hh hsmall z hz
  obtain ⟨hzpos, hsrange, haction⟩ :=
    hDisk E hE r hr h hh (hsmall.trans (min_le_left _ _)) z hz
  refine ⟨hzpos, ?_⟩
  have haction' : bridgeAction b E r - bridgeAction b E (complexLandauEffectiveRadius z) ≤
      A * h := by linarith only [(abs_le.mp haction).1]
  have hquot := (div_le_iff₀ hh).mpr haction'
  have hexponent : -bridgeAction b E (complexLandauEffectiveRadius z) / h ≤
      A + -bridgeAction b E r / h := by
    convert add_le_add_right hquot (-bridgeAction b E r / h) using 1 <;> ring
  calc
    _ ≤ landauKernel b h E (complexLandauEffectiveRadius z) :=
      norm_complexLandauKernel_le hb hh hzpos.le
    _ ≤ C * (h ^ 2)⁻¹ *
        Real.exp (-bridgeAction b E (complexLandauEffectiveRadius z) / h) :=
      hKernel E hE _ hsrange h hh (hsmall.trans (min_le_right _ _))
    _ ≤ C * (h ^ 2)⁻¹ * Real.exp (A + -bridgeAction b E r / h) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- Uniform exact-action Cauchy bounds, with a common constant and threshold
for every derivative order. Only the explicit factorial depends on the order. -/
theorem exists_uniform_complexLandauKernel_iteratedDeriv_bound
    {b Emin Emax rMin rMax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin)
    (hEmax : Emin ≤ Emax) (hMin : 0 < rMin) (hMax : rMin ≤ rMax) :
    ∃ C > 0, ∃ h₀ > 0, ∀ n : ℕ, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rMin rMax,
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ‖iteratedDeriv n (complexLandauKernel b h E) (r : ℂ)‖ ≤
          (n.factorial : ℝ) * C * (h ^ (n + 2))⁻¹ *
            Real.exp (-bridgeAction b E r / h) := by
  obtain ⟨C, hC, h₀, hh₀, hDisk⟩ :=
    exists_uniform_complexLandauKernel_disk_bound hb hEmin hEmax hMin hMax
  refine ⟨C, hC, h₀, hh₀, ?_⟩
  intro n E hE r hr h hh hsmall
  have hEp := hEmin.trans_le hE.1
  have hdomain : closedBall (r : ℂ) h ⊆ complexLandauRadiusDomain :=
    fun z hz => (hDisk E hE r hr h hh hsmall z hz).1
  have hregular := (differentiableOn_complexLandauKernel hb hh hEp).diffContOnCl_ball hdomain
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hh
    hregular (fun z hz => (hDisk E hE r hr h hh hsmall z (sphere_subset_closedBall hz)).2)
  apply hCauchy.trans_eq
  simp only [pow_add, mul_inv_rev, div_eq_mul_inv]
  ring

/-- Restriction to the positive real axis commutes with every radial
derivative after taking the real part. No regularity at radius zero is used. -/
theorem re_iteratedDeriv_complexLandauKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (iteratedDeriv n (complexLandauKernel b h E) (r : ℂ)).re =
      iteratedDeriv n (landauKernel b h E) r := by
  induction n generalizing r with
  | zero => simp only [iteratedDeriv_zero, complexLandauKernel_ofReal, Complex.ofReal_re]
  | succ n ih =>
    have har : AnalyticAt ℂ (complexLandauKernel b h E) (r : ℂ) :=
      analyticOnNhd_complexLandauKernel hb hh hE _ (by
        simpa only [complexLandauRadiusDomain, mem_setOf_eq, ← Complex.ofReal_pow,
          Complex.ofReal_re] using sq_pos_of_pos hr)
    have han : AnalyticAt ℂ (iteratedDeriv n (complexLandauKernel b h E)) (r : ℂ) := by
      rw [iteratedDeriv_eq_iterate]
      exact har.iterated_deriv n
    have hlocal : (fun x : ℝ =>
        (iteratedDeriv n (complexLandauKernel b h E) (x : ℂ)).re) =ᶠ[𝓝 r]
          iteratedDeriv n (landauKernel b h E) := by
      filter_upwards [eventually_gt_nhds hr] with x hx
      exact ih hx
    have hd := han.differentiableAt.hasDerivAt.real_of_complex.congr_of_eventuallyEq
      hlocal.symm
    simpa only [iteratedDeriv_succ] using hd.deriv.symm

/-- The same exact-action estimate holds for the ordinary real radial
derivatives of the original proper-time integral. -/
theorem exists_uniform_landauKernel_iteratedDeriv_bound
    {b Emin Emax rMin rMax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin)
    (hEmax : Emin ≤ Emax) (hMin : 0 < rMin) (hMax : rMin ≤ rMax) :
    ∃ C > 0, ∃ h₀ > 0, ∀ n : ℕ, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rMin rMax,
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ‖iteratedDeriv n (landauKernel b h E) r‖ ≤
          (n.factorial : ℝ) * C * (h ^ (n + 2))⁻¹ *
            Real.exp (-bridgeAction b E r / h) := by
  obtain ⟨C, hC, h₀, hh₀, hbound⟩ :=
    exists_uniform_complexLandauKernel_iteratedDeriv_bound hb hEmin hEmax hMin hMax
  refine ⟨C, hC, h₀, hh₀, ?_⟩
  intro n E hE r hr h hh hsmall
  rw [Real.norm_eq_abs, ← re_iteratedDeriv_complexLandauKernel hb hh
    (hEmin.trans_le hE.1) n (hMin.trans_le hr.1)]
  exact (Complex.abs_re_le_norm _).trans (hbound n E hE r hr h hh hsmall)

end InfiniteZero
