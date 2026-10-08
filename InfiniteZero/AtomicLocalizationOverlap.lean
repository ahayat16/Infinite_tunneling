import InfiniteZero.AtomicLocalizationCutoffs
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Orthogonality error for the actual atomic localization

A bounded real cutoff preserves `L²`. Its failure to preserve orthogonality
is controlled by the mass of the original state outside the region where
the cutoff equals one. The final estimates use the constructed inner cutoff.
-/

noncomputable section
open Set Filter MeasureTheory
namespace InfiniteZero

theorem mass_nonneg (φ : Wavefunction) : 0 ≤ mass φ :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem integrable_waveInner_integrand {φ u : Wavefunction}
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    Integrable (fun x => star (φ x) * u x) volume := by
  simpa only [Pi.star_apply] using hφ.star.integrable_mul hu

theorem norm_waveInner_sq_le_mass_mul {φ u : Wavefunction}
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    ‖waveInner φ u‖ ^ 2 ≤ mass φ * mass u := by
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp φ (ENNReal.ofReal (2 : ℝ)) volume by simpa using hφ)
    (show MemLp u (ENNReal.ofReal (2 : ℝ)) volume by simpa using hu)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hholder
  have hnorm : ‖waveInner φ u‖ ≤ Real.sqrt (mass φ) * Real.sqrt (mass u) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul, norm_star, mass] using hholder
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [mul_pow, Real.sq_sqrt (mass_nonneg φ), Real.sq_sqrt (mass_nonneg u)] using hsq

theorem memLp_real_cutoff_mul {χ : Plane → ℝ} {φ : Wavefunction}
    (hχ : Measurable χ) (hχbound : ∀ x, |χ x| ≤ 1) (hφ : MemLp φ 2 volume) :
    MemLp (fun x => (χ x : ℂ) * φ x) 2 volume := by
  apply hφ.of_le (hχ.complex_ofReal.aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖(χ x : ℂ) * φ x‖ ≤ ‖φ x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hχbound x) (norm_nonneg _)).trans_eq (one_mul _)

theorem memLp_real_cutoff_defect {χ : Plane → ℝ} {φ : Wavefunction}
    (hχ : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1)
    (hφ : MemLp φ 2 volume) :
    MemLp (fun x => ((1 - χ x : ℝ) : ℂ) * φ x) 2 volume := by
  apply memLp_real_cutoff_mul (measurable_const.sub hχ) _ hφ
  intro x
  rw [abs_of_nonneg (sub_nonneg.mpr (hχle x))]
  linarith [hχnonneg x]

theorem mass_real_cutoff_defect_le_setIntegral {χ : Plane → ℝ} {φ : Wavefunction}
    {S : Set Plane} (hS : MeasurableSet S)
    (hχ : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1)
    (hχone : ∀ x, x ∉ S → χ x = 1) (hφ : MemLp φ 2 volume) :
    mass (fun x => ((1 - χ x : ℝ) : ℂ) * φ x) ≤ ∫ x in S, ‖φ x‖ ^ 2 := by
  have hdef := memLp_real_cutoff_defect hχ hχnonneg hχle hφ
  have hnorm (x : Plane) : ‖((1 - χ x : ℝ) : ℂ) * φ x‖ ≤ ‖φ x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hχle x))]
    exact (mul_le_mul_of_nonneg_right (show 1 - χ x ≤ 1 by linarith [hχnonneg x])
      (norm_nonneg _)).trans_eq (one_mul _)
  unfold mass
  rw [← integral_indicator hS]
  apply integral_mono hdef.norm.integrable_sq (hφ.norm.integrable_sq.indicator hS)
  intro x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm x) 2
  · simp [indicator_of_notMem hx, hχone x hx]

theorem waveInner_real_cutoff_eq_sub {χ : Plane → ℝ} {φ u : Wavefunction}
    (hχ : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1)
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    waveInner φ (fun x => (χ x : ℂ) * u x) =
      waveInner φ u - waveInner (fun x => ((1 - χ x : ℝ) : ℂ) * φ x) u := by
  have hdef := memLp_real_cutoff_defect hχ hχnonneg hχle hφ
  unfold waveInner
  rw [← integral_sub (integrable_waveInner_integrand hφ hu)
    (integrable_waveInner_integrand hdef hu)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring

def atomicInnerCutoffDefect (p : CuspParameters) (hr₀ : 0 < p.r₀)
    (φ : Wavefunction) : Wavefunction :=
  fun x => ((1 - p.atomicInnerCutoff hr₀ x : ℝ) : ℂ) * φ x

theorem memLp_atomicInnerCutoff_mul {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {u : Wavefunction} (hu : MemLp u 2 volume) :
    MemLp (fun x => (p.atomicInnerCutoff hr₀ x : ℂ) * u x) 2 volume := by
  apply memLp_real_cutoff_mul (p.atomicInnerCutoff_contDiff hr₀).continuous.measurable _ hu
  intro x
  rw [abs_of_nonneg (p.atomicInnerCutoff_nonneg hr₀ x)]
  exact p.atomicInnerCutoff_le_one hr₀ x

theorem memLp_atomicInnerCutoffDefect {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    MemLp (atomicInnerCutoffDefect p hr₀ φ) 2 volume :=
  memLp_real_cutoff_defect (p.atomicInnerCutoff_contDiff hr₀).continuous.measurable
    (p.atomicInnerCutoff_nonneg hr₀) (p.atomicInnerCutoff_le_one hr₀) hφ

theorem mass_atomicInnerCutoffDefect_le_exterior {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    mass (atomicInnerCutoffDefect p hr₀ φ) ≤
      ∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  apply mass_real_cutoff_defect_le_setIntegral
    (isClosed_le continuous_const continuous_norm).measurableSet
    (p.atomicInnerCutoff_contDiff hr₀).continuous.measurable
    (p.atomicInnerCutoff_nonneg hr₀) (p.atomicInnerCutoff_le_one hr₀) _ hφ
  intro x hx
  apply CuspParameters.atomicInnerCutoff_one hr₀
  have hn : ¬ p.r₀ ≤ ‖x‖ := hx
  linarith [lt_of_not_ge hn]

/-- Exact orthogonality defect for the constructed inner localization. -/
theorem waveInner_atomicInnerCutoff_eq_neg_defect {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {φ u : Wavefunction} (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume)
    (horth : waveInner φ u = 0) :
    waveInner φ (fun x => (p.atomicInnerCutoff hr₀ x : ℂ) * u x) =
      -waveInner (atomicInnerCutoffDefect p hr₀ φ) u := by
  rw [waveInner_real_cutoff_eq_sub (p.atomicInnerCutoff_contDiff hr₀).continuous.measurable
    (p.atomicInnerCutoff_nonneg hr₀) (p.atomicInnerCutoff_le_one hr₀) hφ hu, horth, zero_sub]
  rfl

/-- No spectral estimate is assumed: only `L²` membership and the original
orthogonality are needed for this exterior-mass bound. -/
theorem norm_waveInner_atomicInnerCutoff_sq_le_exterior_mass {p : CuspParameters}
    (hr₀ : 0 < p.r₀) {φ u : Wavefunction}
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) (horth : waveInner φ u = 0) :
    ‖waveInner φ (fun x => (p.atomicInnerCutoff hr₀ x : ℂ) * u x)‖ ^ 2 ≤
      (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) * mass u := by
  rw [waveInner_atomicInnerCutoff_eq_neg_defect hr₀ hφ hu horth, norm_neg]
  exact (norm_waveInner_sq_le_mass_mul (memLp_atomicInnerCutoffDefect hr₀ hφ) hu).trans
    (mul_le_mul_of_nonneg_right (mass_atomicInnerCutoffDefect_le_exterior hr₀ hφ) (mass_nonneg u))

/-- The localization bound for arbitrary `L²` functions retains the original
overlap as a rank-one error; no orthogonality hypothesis is required. -/
theorem norm_waveInner_atomicInnerCutoff_sq_le_overlap_exterior_mass {p : CuspParameters}
    (hr₀ : 0 < p.r₀) {φ u : Wavefunction}
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    ‖waveInner φ (fun x => (p.atomicInnerCutoff hr₀ x : ℂ) * u x)‖ ^ 2 ≤
      2 * ‖waveInner φ u‖ ^ 2 +
        2 * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) * mass u := by
  have hdef : ‖waveInner (atomicInnerCutoffDefect p hr₀ φ) u‖ ^ 2 ≤
      (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) * mass u :=
    (norm_waveInner_sq_le_mass_mul (memLp_atomicInnerCutoffDefect hr₀ hφ) hu).trans
      (mul_le_mul_of_nonneg_right (mass_atomicInnerCutoffDefect_le_exterior hr₀ hφ) (mass_nonneg u))
  rw [waveInner_real_cutoff_eq_sub (p.atomicInnerCutoff_contDiff hr₀).continuous.measurable
    (p.atomicInnerCutoff_nonneg hr₀) (p.atomicInnerCutoff_le_one hr₀) hφ hu]
  change ‖waveInner φ u - waveInner (atomicInnerCutoffDefect p hr₀ φ) u‖ ^ 2 ≤ _
  have htri := pow_le_pow_left₀ (norm_nonneg _)
    (norm_sub_le (waveInner φ u) (waveInner (atomicInnerCutoffDefect p hr₀ φ) u)) 2
  nlinarith [sq_nonneg (‖waveInner φ u‖ - ‖waveInner (atomicInnerCutoffDefect p hr₀ φ) u‖)]

end InfiniteZero
