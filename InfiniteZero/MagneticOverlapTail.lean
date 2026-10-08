import InfiniteZero.ParityTrialStates
import InfiniteZero.AtomicLocalizationOverlap
import InfiniteZero.LocalCompactL2Bound

/-!
# The magnetic overlap is controlled by the radial exterior mass

The magnetic phases have modulus one. If the two centers are separated by
at least twice the cutoff radius, every point is exterior to at least one
center. Cauchy--Schwarz on that measurable partition gives the estimate
using only square integrability and unit mass of the original state.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace InfiniteZero

private theorem norm_waveInner_sq_le_four_of_tail_partition
    {u v : Wavefunction} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hmu : mass u = 1) (hmv : mass v = 1) {s : Set Plane} (hs : MeasurableSet s)
    {M : ℝ} (huM : (∫ x in s, ‖u x‖ ^ 2) ≤ M)
    (hvM : (∫ x in sᶜ, ‖v x‖ ^ 2) ≤ M) :
    ‖waveInner u v‖ ^ 2 ≤ 4 * M := by
  have hleft : waveInner (s.indicator u) v = ∫ x in s, star (u x) * v x := by
    rw [waveInner, ← integral_indicator hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by by_cases hx : x ∈ s <;> simp [hx]
  have hright : waveInner u (sᶜ.indicator v) = ∫ x in sᶜ, star (u x) * v x := by
    rw [waveInner, ← integral_indicator hs.compl]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by by_cases hx : x ∈ s <;> simp [hx]
  have hdecomp : waveInner u v =
      waveInner (s.indicator u) v + waveInner u (sᶜ.indicator v) := by
    rw [hleft, hright]
    exact (integral_add_compl hs (integrable_waveInner_integrand hu hv)).symm
  have h₁ := norm_waveInner_sq_le_mass_mul (hu.indicator hs) hv
  rw [hmv, mul_one, mass_indicator_eq_setIntegral s hs] at h₁
  have h₂ := norm_waveInner_sq_le_mass_mul hu (hv.indicator hs.compl)
  rw [hmu, one_mul, mass_indicator_eq_setIntegral sᶜ hs.compl] at h₂
  have hn : ‖waveInner u v‖ ≤
      ‖waveInner (s.indicator u) v‖ + ‖waveInner u (sᶜ.indicator v)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖waveInner (s.indicator u) v‖ -
    ‖waveInner u (sᶜ.indicator v)‖)]

theorem norm_waveInner_leftState_rightState_sq_le_tail
    (b coupling : ℝ) {a L : ℝ} (ha : 0 < a) (hL : a ≤ L)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hm : mass φ = 1) :
    ‖waveInner (leftState b L coupling φ) (rightState b L coupling φ)‖ ^ 2 ≤
      4 * ∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  let d := displacement L
  let S : Set Plane := {x | a ≤ ‖x + d‖}
  let U : Set Plane := {x | a ≤ ‖d - x‖}
  let E : Set Plane := {x | a ≤ ‖x‖}
  have hS : MeasurableSet S := (isClosed_le continuous_const
    (continuous_id.add continuous_const).norm).measurableSet
  have hU : MeasurableSet U := (isClosed_le continuous_const
    (continuous_const.sub continuous_id).norm).measurableSet
  have hE : MeasurableSet E := (isClosed_le continuous_const continuous_norm).measurableSet
  have hleft (x : Plane) : ‖leftState b L coupling φ x‖ = ‖φ (x + d)‖ := by
    simp only [leftState, norm_magneticTranslation, sub_neg_eq_add, d]
  have hright (x : Plane) : ‖rightState b L coupling φ x‖ = ‖φ (d - x)‖ := by
    simp only [rightState, leftState, norm_magneticTranslation, sub_neg_eq_add,
      neg_add_eq_sub, d]
  have htailLeft : (∫ x in S, ‖leftState b L coupling φ x‖ ^ 2) =
      ∫ x in E, ‖φ x‖ ^ 2 := by
    calc
      _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) (x + d) := by
        rw [← integral_indicator hS]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          by_cases hx : a ≤ ‖x + d‖ <;> simp [S, E, hx, hleft]
      _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) x :=
        integral_add_right_eq_self _ d
      _ = _ := integral_indicator hE
  have htailRight : (∫ x in U, ‖rightState b L coupling φ x‖ ^ 2) =
      ∫ x in E, ‖φ x‖ ^ 2 := by
    calc
      _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) (d - x) := by
        rw [← integral_indicator hU]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          by_cases hx : a ≤ ‖d - x‖ <;> simp [U, E, hx, hright]
      _ = ∫ x : Plane, E.indicator (fun y => ‖φ y‖ ^ 2) x :=
        integral_sub_left_eq_self _ volume d
      _ = _ := integral_indicator hE
  have hcover : Sᶜ ⊆ U := by
    intro x hx
    have hxlt : ‖x + d‖ < a := lt_of_not_ge hx
    have hd : ‖2 • d‖ = 2 * L := by
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      simp [d, displacement, coordinateVector, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (ha.le.trans hL)]
    have htriangle := norm_add_le (x + d) (d - x)
    rw [show x + d + (d - x) = 2 • d by simp [two_smul]; abel, hd] at htriangle
    change a ≤ ‖d - x‖
    linarith
  have hLpLeft := memLp_leftState b L coupling hφ
  have hLpRight := memLp_rightState b L coupling hφ
  have hmLeft : mass (leftState b L coupling φ) = 1 := by
    exact (mass_magneticTranslation b coupling (-displacement L) φ).trans hm
  have hmRight : mass (rightState b L coupling φ) = 1 :=
    (mass_inversion (leftState b L coupling φ)).trans hmLeft
  apply norm_waveInner_sq_le_four_of_tail_partition hLpLeft hLpRight hmLeft hmRight hS
    htailLeft.le
  calc
    _ ≤ ∫ x in U, ‖rightState b L coupling φ x‖ ^ 2 :=
      setIntegral_mono_set hLpRight.norm.integrable_sq.integrableOn
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hcover)
    _ = _ := htailRight

theorem norm_waveInner_leftState_rightState_le_sqrt_tail
    (b coupling : ℝ) {a L : ℝ} (ha : 0 < a) (hL : a ≤ L)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hm : mass φ = 1) :
    ‖waveInner (leftState b L coupling φ) (rightState b L coupling φ)‖ ≤
      2 * Real.sqrt (∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2) := by
  have hsq := norm_waveInner_leftState_rightState_sq_le_tail b coupling ha hL hφ hm
  have hmext : 0 ≤ ∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  nlinarith [Real.sq_sqrt hmext, Real.sqrt_nonneg
    (∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2)]

end InfiniteZero
