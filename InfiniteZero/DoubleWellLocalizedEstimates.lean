import InfiniteZero.LocalizedOverlap
import InfiniteZero.MagneticLocalizedForm
import InfiniteZero.DoubleWellLocalizationCutoffs

/-!
# Localized overlaps and forms for the fixed double-well cutoffs

The overlap losses are controlled by the original atomic mass outside
`4 r₀`. The local forms see exactly the corresponding well, and the
exterior form is nonnegative. No spectral input is used in this module.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem norm_waveInner_doubleWellLeftCutoff_sq_le
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (L coupling : ℝ) {φ u : Wavefunction}
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    ‖waveInner (leftState p.b L coupling φ)
      (fun x => (doubleWellLeftCutoff hp cert L x : ℂ) * u x)‖ ^ 2 ≤
        2 * ‖waveInner (leftState p.b L coupling φ) u‖ ^ 2 +
          2 * (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) * mass u := by
  have hS : MeasurableSet {x : Plane | 4 * p.r₀ ≤ ‖x + displacement L‖} :=
    (isClosed_le continuous_const (continuous_id.add continuous_const).norm).measurableSet
  have hplateau : ∀ x : Plane, x ∉ {x : Plane | 4 * p.r₀ ≤ ‖x + displacement L‖} →
      doubleWellLeftCutoff hp cert L x = 1 := by
    intro x hx
    exact doubleWellLeftCutoff_one_on_coreBall hp cert L (lt_of_not_ge hx).le
  have hb := norm_waveInner_real_cutoff_sq_le_overlap_setIntegral hS
    (doubleWellLeftCutoff_contDiff hp cert L).continuous.measurable
    (fun x => (doubleWellCutoffs_range hp cert L x).1.1)
    (fun x => (doubleWellCutoffs_range hp cert L x).1.2)
    hplateau (memLp_leftState p.b L coupling hφ) hu
  rw [setIntegral_leftState_tail] at hb
  exact hb

theorem norm_waveInner_doubleWellRightCutoff_sq_le
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (L coupling : ℝ) {φ u : Wavefunction}
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    ‖waveInner (rightState p.b L coupling φ)
      (fun x => (doubleWellRightCutoff hp cert L x : ℂ) * u x)‖ ^ 2 ≤
        2 * ‖waveInner (rightState p.b L coupling φ) u‖ ^ 2 +
          2 * (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) * mass u := by
  have hS : MeasurableSet {x : Plane | 4 * p.r₀ ≤ ‖displacement L - x‖} :=
    (isClosed_le continuous_const (continuous_const.sub continuous_id).norm).measurableSet
  have hplateau : ∀ x : Plane, x ∉ {x : Plane | 4 * p.r₀ ≤ ‖displacement L - x‖} →
      doubleWellRightCutoff hp cert L x = 1 := by
    intro x hx
    apply doubleWellRightCutoff_one_on_coreBall hp cert L
    rw [norm_sub_rev]
    exact (lt_of_not_ge hx).le
  have hb := norm_waveInner_real_cutoff_sq_le_overlap_setIntegral hS
    (doubleWellRightCutoff_contDiff hp cert L).continuous.measurable
    (fun x => (doubleWellCutoffs_range hp cert L x).2.1.1)
    (fun x => (doubleWellCutoffs_range hp cert L x).2.1.2)
    hplateau (memLp_rightState p.b L coupling hφ) hu
  rw [setIntegral_rightState_tail] at hb
  exact hb

theorem doubleWellLeftCutoff_form_eq {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L)
    (coupling : ℝ) (ψ : Wavefunction) :
    magneticForm p.b coupling (doubleWellPotential p.potential L)
      (fun x => (doubleWellLeftCutoff hp cert L x : ℂ) * ψ x) =
    magneticForm p.b coupling (fun x => p.potential (x + displacement L))
      (fun x => (doubleWellLeftCutoff hp cert L x : ℂ) * ψ x) :=
  magneticForm_real_cutoff_eq_of_potential_mul_eq p.b coupling
    (doubleWellPotential_mul_leftCutoff hp cert hL) ψ

theorem doubleWellRightCutoff_form_eq {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L)
    (coupling : ℝ) (ψ : Wavefunction) :
    magneticForm p.b coupling (doubleWellPotential p.potential L)
      (fun x => (doubleWellRightCutoff hp cert L x : ℂ) * ψ x) =
    magneticForm p.b coupling (fun x => p.potential (displacement L - x))
      (fun x => (doubleWellRightCutoff hp cert L x : ℂ) * ψ x) := by
  apply magneticForm_real_cutoff_eq_of_potential_mul_eq p.b coupling _ ψ
  intro x
  simpa only [neg_add_eq_sub] using doubleWellPotential_mul_rightCutoff hp cert hL x

/-- No separation assumption is needed for the exterior identity: this
cutoff vanishes on each potential support by its definition. -/
theorem doubleWellExteriorCutoff_form_nonneg {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) (L coupling : ℝ)
    (ψ : Wavefunction) :
    0 ≤ magneticForm p.b coupling (doubleWellPotential p.potential L)
      (fun x => (doubleWellExteriorCutoff hp cert L x : ℂ) * ψ x) :=
  magneticForm_real_cutoff_nonneg_of_potential_mul_zero p.b coupling
    (doubleWellPotential_mul_exteriorCutoff hp cert L) ψ

end InfiniteZero.CuspParameters
