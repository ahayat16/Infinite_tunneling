import InfiniteZero.AtomicLocalizationOverlap
import InfiniteZero.ParityTrialStates

/-!
# Localized overlap errors and translated atomic tails

A real cutoff taking values in `[0,1]` changes an overlap by at most the
mass of the reference state where the cutoff is not one. The translated
tail identities keep that error equal to the original atomic tail, with
no dependence on the well separation or magnetic phase.
-/

noncomputable section
open Set Filter MeasureTheory
namespace InfiniteZero

theorem norm_waveInner_real_cutoff_sq_le_overlap_setIntegral
    {χ : Plane → ℝ} {φ u : Wavefunction} {S : Set Plane}
    (hS : MeasurableSet S) (hχ : Measurable χ)
    (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1)
    (hχone : ∀ x, x ∉ S → χ x = 1)
    (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    ‖waveInner φ (fun x => (χ x : ℂ) * u x)‖ ^ 2 ≤
      2 * ‖waveInner φ u‖ ^ 2 +
        2 * (∫ x in S, ‖φ x‖ ^ 2) * mass u := by
  let δ : Wavefunction := fun x => ((1 - χ x : ℝ) : ℂ) * φ x
  have hδ : MemLp δ 2 volume := memLp_real_cutoff_defect hχ hχnonneg hχle hφ
  have hb : ‖waveInner δ u‖ ^ 2 ≤ (∫ x in S, ‖φ x‖ ^ 2) * mass u :=
    (norm_waveInner_sq_le_mass_mul hδ hu).trans
      (mul_le_mul_of_nonneg_right
        (mass_real_cutoff_defect_le_setIntegral hS hχ hχnonneg hχle hχone hφ)
        (mass_nonneg u))
  rw [waveInner_real_cutoff_eq_sub hχ hχnonneg hχle hφ hu]
  change ‖waveInner φ u - waveInner δ u‖ ^ 2 ≤ _
  have htri := pow_le_pow_left₀ (norm_nonneg _)
    (norm_sub_le (waveInner φ u) (waveInner δ u)) 2
  nlinarith [sq_nonneg (‖waveInner φ u‖ - ‖waveInner δ u‖)]

theorem setIntegral_leftState_tail (b L coupling a : ℝ) (φ : Wavefunction) :
    (∫ x in {x : Plane | a ≤ ‖x + displacement L‖},
      ‖leftState b L coupling φ x‖ ^ 2) =
        ∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  let S : Set Plane := {x | a ≤ ‖x + displacement L‖}
  let E : Set Plane := {x | a ≤ ‖x‖}
  have hS : MeasurableSet S := (isClosed_le continuous_const
    (continuous_id.add continuous_const).norm).measurableSet
  have hE : MeasurableSet E := (isClosed_le continuous_const continuous_norm).measurableSet
  calc
    _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) (x + displacement L) := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : a ≤ ‖x + displacement L‖ <;>
          simp [S, E, hx, leftState, norm_magneticTranslation]
    _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) x :=
      integral_add_right_eq_self _ (displacement L)
    _ = _ := integral_indicator hE

theorem setIntegral_rightState_tail (b L coupling a : ℝ) (φ : Wavefunction) :
    (∫ x in {x : Plane | a ≤ ‖displacement L - x‖},
      ‖rightState b L coupling φ x‖ ^ 2) =
        ∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  let S : Set Plane := {x | a ≤ ‖displacement L - x‖}
  let E : Set Plane := {x | a ≤ ‖x‖}
  have hS : MeasurableSet S := (isClosed_le continuous_const
    (continuous_const.sub continuous_id).norm).measurableSet
  have hE : MeasurableSet E := (isClosed_le continuous_const continuous_norm).measurableSet
  calc
    _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) (displacement L - x) := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : a ≤ ‖displacement L - x‖ <;>
          simp [S, E, hx, rightState, leftState, norm_magneticTranslation, neg_add_eq_sub]
    _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) x :=
      integral_sub_left_eq_self _ volume (displacement L)
    _ = _ := integral_indicator hE

end InfiniteZero
