import InfiniteZero.HoppingChannels
import InfiniteZero.ConstructionSmooth
import InfiniteZero.ConstructionCuspBounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Absolute convergence of the nine physical source cells

This uses the actual smooth compact sources and the outgoing horizontal
geometry of the chosen potential. No spectral or tunneling estimate is
assumed. The scalar kernel is measurable directly from its integral formula.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace InfiniteZero

theorem measurable_landauKernel (b h E : ℝ) : Measurable (landauKernel b h E) := by
  have hm : Measurable (fun q : ℝ × ℝ => landauIntegrand b h E q.1 q.2) := by
    unfold landauIntegrand properTimePhase
    fun_prop
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_sourceKernel (b L h E : ℝ) :
    Measurable (fun q : Plane × Plane => sourceKernel b L h E q.1 q.2) := by
  unfold sourceKernel
  have hk := (measurable_landauKernel b h E).comp
    (show Measurable (fun q : Plane × Plane => ‖q.1 + q.2 - 2 • displacement L‖) by fun_prop)
  apply hk.complex_ofReal.mul
  unfold sourcePhase
  fun_prop

theorem norm_sourceKernel {b h E : ℝ} (hb : 0 < b) (hh : 0 < h) (hE : 0 < E)
    (L : ℝ) (z w : Plane) (hr : 0 < ‖z + w - 2 • displacement L‖) :
    ‖sourceKernel b L h E z w‖ = landauKernel b h E ‖z + w - 2 • displacement L‖ := by
  simp only [sourceKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (landauKernel_pos hb hh hE hr)]
  rw [Complex.norm_exp]
  simp

theorem plane_coordinate_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have hs : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [sq_abs, EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hs

theorem bridge_distance_ge_horizontal (z w : Plane) (L : ℝ) :
    2 * L - z 0 - w 0 ≤ ‖z + w - 2 • displacement L‖ := by
  have hc := (neg_le_abs ((z + w - 2 • displacement L) 0)).trans
    (plane_coordinate_le_norm (z + w - 2 • displacement L) 0)
  simp [displacement, coordinateVector] at hc ⊢
  linarith

theorem componentPotential_continuous {p : CuspParameters} (hp : p.BasicConditions) (i : Fin 3) :
    Continuous (componentPotential p i) := by
  fin_cases i
  · exact (CuspParameters.core_contDiff hp.r₀_pos).continuous
  · exact continuous_const.mul (CuspParameters.cuspPlus_contDiff hp).continuous
  · exact continuous_const.mul (CuspParameters.cuspMinus_contDiff hp).continuous

theorem componentPotential_hasCompactSupport {p : CuspParameters}
    (hp : p.BasicConditions) (i : Fin 3) : HasCompactSupport (componentPotential p i) := by
  fin_cases i
  · exact CuspParameters.core_hasCompactSupport p
  · exact (CuspParameters.cuspPlus_hasCompactSupport hp).mul_left
  · exact (CuspParameters.cuspMinus_hasCompactSupport hp).mul_left

theorem componentPotential_support_horizontal {p : CuspParameters} (hp : p.BasicConditions)
    (i : Fin 3) {x : Plane} (hx : componentPotential p i x ≠ 0) : x 0 ≤ p.R / 2 := by
  fin_cases i
  · have hc : x ∈ tsupport p.core := subset_tsupport p.core hx
    have hn := CuspParameters.core_tsupport_subset_closedBall p hc
    rw [Metric.mem_closedBall, dist_zero_right] at hn
    have hcoord := (le_abs_self (x 0)).trans (plane_coordinate_le_norm x 0)
    linarith [hp.radius_large, hp.r₀_pos]
  · have hc : x ∈ tsupport p.cuspPlus := subset_tsupport p.cuspPlus
      (right_ne_zero_of_mul (by simpa [componentPotential] using hx))
    have ht := (CuspParameters.cuspPlus_tsupport_subset_quadratic p hc).1
    have hh := CuspParameters.cuspPlus_tsupport_horizontal hp hc
    linarith
  · have hc : x ∈ tsupport p.cuspMinus := subset_tsupport p.cuspMinus
      (right_ne_zero_of_mul (by simpa [componentPotential] using hx))
    have href : CuspParameters.reflection x ∈ tsupport p.cuspPlus :=
      tsupport_comp_subset_preimage p.cuspPlus CuspParameters.reflection_contDiff.continuous hc
    have ht := (CuspParameters.cuspPlus_tsupport_subset_quadratic p href).1
    have hh := (CuspParameters.cuspMinus_tsupport_outgoing_bounds hp hc).1
    linarith

theorem componentSource_continuous {p : CuspParameters} (hp : p.BasicConditions)
    (h : ℝ) {φ : Wavefunction} (hφ : Continuous φ) (i : Fin 3) :
    Continuous (componentSource p h φ i) := by
  exact (Complex.continuous_ofReal.comp
    (continuous_const.mul (componentPotential_continuous hp i))).mul hφ

theorem componentSource_hasCompactSupport {p : CuspParameters} (hp : p.BasicConditions)
    (h : ℝ) (φ : Wavefunction) (i : Fin 3) : HasCompactSupport (componentSource p h φ i) := by
  apply HasCompactSupport.intro (componentPotential_hasCompactSupport hp i)
  intro x hx
  have hz := image_eq_zero_of_notMem_tsupport hx
  simp [componentSource, atomicSource, hz]

theorem componentSource_integrable {p : CuspParameters} (hp : p.BasicConditions)
    (h : ℝ) {φ : Wavefunction} (hφ : Continuous φ) (i : Fin 3) :
    Integrable (componentSource p h φ i) :=
  (componentSource_continuous hp h hφ i).integrable_of_hasCompactSupport
    (componentSource_hasCompactSupport hp h φ i)

theorem cellsIntegrable_of_continuous {p : CuspParameters} (hp : p.BasicConditions)
    {L h E : ℝ} (hL : p.R < 2 * L) (hh : 0 < h) (hE : 0 < E)
    {φ : Wavefunction} (hφ : Continuous φ) : CellsIntegrable p L h E φ := by
  intro i j
  let F := componentSource p h φ i
  let G := componentSource p h φ j
  let C := 1 / (Real.pi * E * (2 * L - p.R) ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hF := componentSource_integrable hp h hφ i
  have hG := componentSource_integrable hp h hφ j
  have hmaj := (hF.norm.mul_prod hG.norm).const_mul C
  have hm : AEStronglyMeasurable (channelIntegrand (sourceKernel p.b L h E) F G)
      (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    unfold channelIntegrand
    have hFm : Measurable (fun q : Plane × Plane => F q.1) :=
      (componentSource_continuous hp h hφ i).measurable.comp measurable_fst
    have hGm : Measurable (fun q : Plane × Plane => G q.2) :=
      (componentSource_continuous hp h hφ j).measurable.comp measurable_snd
    simpa only [Complex.star_def] using
      ((Complex.continuous_conj.measurable.comp hFm).mul
        (measurable_sourceKernel p.b L h E)).mul hGm
  apply hmaj.mono' hm
  apply Filter.Eventually.of_forall
  intro q
  by_cases hFi : F q.1 = 0
  · simp only [channelIntegrand, hFi, star_zero, zero_mul, norm_zero]
    positivity
  by_cases hGj : G q.2 = 0
  · simp only [channelIntegrand, hGj, mul_zero, norm_zero]
    positivity
  have hi : componentPotential p i q.1 ≠ 0 := by
    intro hz
    apply hFi
    simp [F, componentSource, atomicSource, hz]
  have hj : componentPotential p j q.2 ≠ 0 := by
    intro hz
    apply hGj
    simp [G, componentSource, atomicSource, hz]
  have hr : 2 * L - p.R ≤ ‖q.1 + q.2 - 2 • displacement L‖ := by
    have h₁ := componentPotential_support_horizontal hp i hi
    have h₂ := componentPotential_support_horizontal hp j hj
    linarith [bridge_distance_ge_horizontal q.1 q.2 L]
  have hrpos : 0 < ‖q.1 + q.2 - 2 • displacement L‖ := lt_of_lt_of_le (sub_pos.mpr hL) hr
  have hK : ‖sourceKernel p.b L h E q.1 q.2‖ ≤ C := by
    rw [norm_sourceKernel hp.b_pos hh hE L q.1 q.2 hrpos]
    apply (landauKernel_le hp.b_pos hh hE hrpos).trans
    dsimp [C]
    gcongr
  dsimp only [channelIntegrand]
  rw [norm_mul, norm_mul, norm_star]
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hK (norm_nonneg (F q.1))) (norm_nonneg (G q.2))]

theorem canonicalAtomicState_contDiff (b : ℝ) (v : Potential) (coupling : ℝ) :
    ContDiff ℝ ∞ (canonicalAtomicState b v coupling) := by
  classical
  by_cases h : ∃ φ, IsAtomicGroundState b v coupling φ
  · exact (canonicalAtomicState_spec b v coupling h).1.1
  · simp only [canonicalAtomicState, dif_neg h]
    exact contDiff_const

end InfiniteZero
