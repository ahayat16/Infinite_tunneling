import InfiniteZero.AtomicSmoothWeightedGraph
import InfiniteZero.AtomicWeightedTail
import InfiniteZero.CuspWeightApproximation
import InfiniteZero.BoundedMultiplierLimits

/-!
# Weighted graph coercivity for the exact cusp weight

The smooth positive-part approximations have one common bound on their
gradients. Their exponential multiplication operators converge strongly to
the multiplier of the exact Lipschitz cusp weight. Passing to this limit
retains the radial rank-one defect on the actual closed operator graph.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

namespace CuspWeightCutoffs

variable {p : CuspParameters} (χ : CuspWeightCutoffs p)

theorem weight_continuous : Continuous χ.weight := by
  obtain ⟨C, hC⟩ := χ.weight_lipschitz
  exact hC.continuous

theorem tendsto_smoothWeight (x : Plane) :
    Tendsto (fun n : ℕ => χ.smoothWeight (1 / ((n : ℝ) + 1)) x) atTop
      (𝓝 (χ.weight x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.norm_eq_abs]
  exact χ.smoothWeight_abs_sub_weight_le (by positivity) x

end CuspWeightCutoffs

/-- The constants and coupling threshold precede the coupling; the radial
reference state precedes the weight strength. No claim that the weighted
vector belongs to the operator domain is needed. -/
theorem exists_atomic_cusp_weighted_graph_lower_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) :
    ∃ M > 0, ∃ hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ threshold > 0, ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ : Wavefunction, ∃ hφ : IsAtomicGroundState p.b p.core coupling φ,
      IsPositiveRadial φ ∧
      ∀ κ ∈ Icc 0 κ₀,
      let W := atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
      ∀ u : (magneticOperator p.b coupling p.potential).domain,
        (hRad.gap / 2 * coupling) * ‖W (u : L2Space)‖ ^ 2 -
            2 * (hRad.gap * coupling) * ‖inner ℂ (hφ.1.2.1.toLp φ) (W (u : L2Space))‖ ^ 2 ≤
          (inner ℂ (W (u : L2Space)) (W (magneticOperator p.b coupling p.potential u))).re -
            atomicGroundEnergy p.b p.core coupling * ‖W (u : L2Space)‖ ^ 2 := by
  obtain ⟨M, hM, G, hG, hunif⟩ := χ.exists_smoothWeight_uniform_bounds
  have hT : ∀ x, χ.weight x ∈ Icc 0 M := by
    intro x
    refine ⟨χ.weight_nonneg x, ?_⟩
    have h := χ.smoothWeight_sub_weight_bounds (ε := 1) (by norm_num) x
    have hu := (hunif 1 (by norm_num) x).1.2
    linarith only [h.1, hu]
  let κ₀ : ℝ := 1 / Real.sqrt (8 * G)
  have hsqrt : 0 < Real.sqrt (8 * G) := Real.sqrt_pos.mpr (by positivity)
  have hκ₀ : 0 < κ₀ := one_div_pos.mpr hsqrt
  have hκ₀sq : κ₀ ^ 2 * G = 1 / 8 := by
    dsimp only [κ₀]
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    field_simp
  obtain ⟨threshold, hthreshold, hsmooth⟩ :=
    exists_atomic_smooth_weighted_graph_lower_of_radialData hp hRad hAcore hApot
  refine ⟨M, hM, hT, κ₀, hκ₀, threshold, hthreshold, ?_⟩
  intro coupling hc
  obtain ⟨φ, hφ, hpos, hgraph⟩ := hsmooth coupling hc
  refine ⟨φ, hφ, hpos, ?_⟩
  intro κ hκ W u
  have hκsq : κ ^ 2 * G ≤ 1 / 8 := by
    rw [← hκ₀sq]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hκ.1 hκ₀.le).mpr hκ.2) hG.le
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : ε n ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp only [ε]; positivity
    · dsimp only [ε]
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let Tn : ℕ → Plane → ℝ := fun n => χ.smoothWeight (ε n)
  have hTn_smooth (n : ℕ) : ContDiff ℝ ∞ (Tn n) :=
    χ.smoothWeight_contDiff (hε n).1
  have hTn (n : ℕ) : ∀ x, Tn n x ∈ Icc 0 M := fun x =>
    (hunif (ε n) (hε n) x).1
  let Wn : ℕ → L2Space →L[ℂ] L2Space := fun n =>
    atomicExponentialWeightMul (Tn n) (hTn_smooth n).continuous (hTn n) coupling κ
  have hWn : ∀ v, Tendsto (fun n => Wn n v) atTop (𝓝 (W v)) := by
    intro v
    apply tendsto_boundedPotentialMul_apply
      (fun n x => Real.exp (κ * coupling * Tn n x))
      (fun x => Real.exp (κ * coupling * χ.weight x))
      (fun n => by fun_prop)
      (Real.continuous_exp.comp (continuous_const.mul χ.weight_continuous))
      (fun n => abs_atomicExponentialWeight_le (hTn n) coupling κ)
      (abs_atomicExponentialWeight_le hT coupling κ) ?_ v
    intro x
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((χ.tendsto_smoothWeight x).const_mul (κ * coupling))
  apply weighted_rankOne_lower_of_strong_limit Wn W hWn
    (hφ.1.2.1.toLp φ) (u : L2Space) (magneticOperator p.b coupling p.potential u)
    (hRad.gap / 2 * coupling) (2 * (hRad.gap * coupling))
    (atomicGroundEnergy p.b p.core coupling)
  intro n
  have hF : ContDiff ℝ ∞ (fun x => κ * coupling * Tn n x) :=
    contDiff_const.mul (hTn_smooth n)
  have hzero : ∀ x, ‖x‖ ≤ 4 * p.r₀ → κ * coupling * Tn n x = 0 := by
    intro x hx
    rw [show Tn n x = 0 from χ.smoothWeight_zero_on_core (ε n) hx, mul_zero]
  have hgrad : ∀ x, cutoffGradientSq (fun y => κ * coupling * Tn n y) x ≤
      coupling ^ 2 / 8 := by
    intro x
    rw [cutoffGradientSq_const_mul _ ((hTn_smooth n).differentiable (by simp) x)]
    have h₁ := mul_le_mul_of_nonneg_left (hunif (ε n) (hε n) x).2
      (sq_nonneg (κ * coupling))
    have h₂ := mul_le_mul_of_nonneg_left hκsq (sq_nonneg coupling)
    nlinarith only [h₁, h₂]
  exact hgraph (fun x => κ * coupling * Tn n x) hF hzero hgrad
    (Real.exp (|κ * coupling| * M)) (abs_atomicExponentialWeight_le (hTn n) coupling κ) u

end InfiniteZero.CuspParameters
