import InfiniteZero.CuspWeight
import InfiniteZero.SmoothPositivePart
import InfiniteZero.MagneticLocalEnergy
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniformly controlled smooth approximations of the cusp weight

The cutoffs remain fixed while the positive part of each normal coordinate
is smoothed. The approximation is nonnegative and still vanishes near the
core. Both its height and squared gradient admit bounds independent of the
smoothing parameter in `(0,1]`.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

private theorem exists_cutoff_smoothPositivePart_fderiv_bound
    {χ ν : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχrange : ∀ x, χ x ∈ Icc 0 1) (hν : ContDiff ℝ ∞ ν) :
    ∃ B > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x,
      ‖fderiv ℝ (fun y => χ y * smoothPositivePart ε (ν y)) x‖ ≤ B := by
  have hK : IsCompact (tsupport χ) := hc
  obtain ⟨Bχ, hBχ, hbχ⟩ := ((hc.fderiv ℝ).isCompact_range
    (hχ.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  obtain ⟨Bν, hBν, hbν⟩ := (hK.image hν.continuous).isBounded.exists_pos_norm_le
  obtain ⟨BD, hBD, hbD⟩ :=
    (hK.image (hν.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨BD + (Bν + 1) * Bχ, by positivity, ?_⟩
  intro ε hε hε1 x
  by_cases hx : x ∈ tsupport χ
  · have hdχ := hχ.differentiable (by simp) x
    have hdν := hν.differentiable (by simp) x
    have hdS := (smoothPositivePart_contDiff hε).differentiable (by simp) (ν x)
    have hcomp : ‖fderiv ℝ (fun y => smoothPositivePart ε (ν y)) x‖ ≤ BD := by
      rw [fderiv_comp' x hdS hdν]
      calc
        _ ≤ ‖fderiv ℝ (smoothPositivePart ε) (ν x)‖ * ‖fderiv ℝ ν x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * ‖fderiv ℝ ν x‖ := mul_le_mul_of_nonneg_right
          (norm_fderiv_le_of_lipschitz ℝ (smoothPositivePart_lipschitz hε)) (norm_nonneg _)
        _ ≤ BD := by rw [one_mul]; exact hbD _ ⟨x, hx, rfl⟩
    have hνval : |ν x| ≤ Bν := by
      simpa only [Real.norm_eq_abs] using hbν _ ⟨x, hx, rfl⟩
    have hmax : max (ν x) 0 ≤ Bν :=
      max_le ((le_abs_self _).trans hνval) hBν.le
    have hSval : ‖smoothPositivePart ε (ν x)‖ ≤ Bν + 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (smoothPositivePart_nonneg _ _)]
      have h := (smoothPositivePart_sub_max_bounds hε.le (ν x)).2
      linarith only [h, hmax, hε1]
    have hχval : ‖χ x‖ ≤ (1 : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1] using (hχrange x).2
    have hdcomp : DifferentiableAt ℝ (fun y => smoothPositivePart ε (ν y)) x :=
      hdS.comp x hdν
    rw [fderiv_fun_mul hdχ hdcomp]
    calc
      _ ≤ ‖χ x • fderiv ℝ (fun y => smoothPositivePart ε (ν y)) x‖ +
          ‖smoothPositivePart ε (ν x) • fderiv ℝ χ x‖ := norm_add_le _ _
      _ = ‖χ x‖ * ‖fderiv ℝ (fun y => smoothPositivePart ε (ν y)) x‖ +
          ‖smoothPositivePart ε (ν x)‖ * ‖fderiv ℝ χ x‖ := by rw [norm_smul, norm_smul]
      _ ≤ 1 * BD + (Bν + 1) * Bχ := add_le_add
        (mul_le_mul hχval hcomp (norm_nonneg _) (by norm_num))
        (mul_le_mul hSval (hbχ _ ⟨x, rfl⟩) (norm_nonneg _) (by positivity))
      _ = _ := by rw [one_mul]
  · have hzero : x ∉ tsupport (fun y => χ y * smoothPositivePart ε (ν y)) :=
      fun h => hx (tsupport_mul_subset_left h)
    rw [fderiv_of_notMem_tsupport ℝ hzero, norm_zero]
    positivity

namespace CuspParameters.CuspWeightCutoffs

variable {p : CuspParameters} (χ : CuspWeightCutoffs p)

def smoothWeight (ε : ℝ) (x : Plane) : ℝ :=
  χ.plus x * smoothPositivePart ε (p.normalCoordinate x) +
    χ.minus x * smoothPositivePart ε (p.normalCoordinate (reflection x))

theorem smoothWeight_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (χ.smoothWeight ε) :=
  (χ.plus_smooth.mul ((smoothPositivePart_contDiff hε).comp
    (normalCoordinate_contDiff p))).add
    (χ.minus_smooth.mul ((smoothPositivePart_contDiff hε).comp
      ((normalCoordinate_contDiff p).comp reflection_contDiff)))

theorem smoothWeight_hasCompactSupport (ε : ℝ) :
    HasCompactSupport (χ.smoothWeight ε) :=
  χ.plus_compact.mul_right.add χ.minus_compact.mul_right

theorem smoothWeight_nonneg (ε : ℝ) (x : Plane) : 0 ≤ χ.smoothWeight ε x :=
  add_nonneg (mul_nonneg (χ.plus_range x).1 (smoothPositivePart_nonneg _ _))
    (mul_nonneg (χ.minus_range x).1 (smoothPositivePart_nonneg _ _))

theorem smoothWeight_zero_on_core (ε : ℝ) {x : Plane} (hx : ‖x‖ ≤ 4 * p.r₀) :
    χ.smoothWeight ε x = 0 := by
  simp only [smoothWeight, χ.plus_zero_on_core hx, χ.minus_zero_on_core hx,
    zero_mul, zero_add]

theorem smoothWeight_sub_weight_bounds {ε : ℝ} (hε : 0 ≤ ε) (x : Plane) :
    0 ≤ χ.smoothWeight ε x - χ.weight x ∧
      χ.smoothWeight ε x - χ.weight x ≤ ε := by
  have hp := smoothPositivePart_sub_max_bounds hε (p.normalCoordinate x)
  have hm := smoothPositivePart_sub_max_bounds hε (p.normalCoordinate (reflection x))
  have hpn := mul_nonneg (χ.plus_range x).1 hp.1
  have hmn := mul_nonneg (χ.minus_range x).1 hm.1
  have hpu := (mul_le_mul_of_nonneg_left hp.2 (χ.plus_range x).1).trans
    (mul_le_of_le_one_left (by positivity : 0 ≤ ε / 2) (χ.plus_range x).2)
  have hmu := (mul_le_mul_of_nonneg_left hm.2 (χ.minus_range x).1).trans
    (mul_le_of_le_one_left (by positivity : 0 ≤ ε / 2) (χ.minus_range x).2)
  simp only [smoothWeight, weight]
  constructor <;> nlinarith only [hpn, hmn, hpu, hmu]

theorem smoothWeight_abs_sub_weight_le {ε : ℝ} (hε : 0 ≤ ε) (x : Plane) :
    |χ.smoothWeight ε x - χ.weight x| ≤ ε := by
  obtain ⟨hlo, hhi⟩ := χ.smoothWeight_sub_weight_bounds hε x
  rwa [abs_of_nonneg hlo]

/-- The height bound is chosen before the smoothing parameter. -/
theorem exists_smoothWeight_bound :
    ∃ M > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x, χ.smoothWeight ε x ∈ Icc 0 M := by
  obtain ⟨L, hL⟩ := χ.weight_lipschitz
  obtain ⟨M, hM, hb⟩ := (χ.weight_hasCompactSupport.isCompact_range hL.continuous).isBounded.exists_pos_norm_le
  refine ⟨M + 1, by positivity, fun ε hε hε1 x => ⟨χ.smoothWeight_nonneg ε x, ?_⟩⟩
  have h := (χ.smoothWeight_sub_weight_bounds hε.le x).2
  have hweight : χ.weight x ≤ M := (le_abs_self _).trans (hb _ ⟨x, rfl⟩)
  linarith only [h, hweight, hε1]

/-- The gradient bound is uniform over every smoothing parameter in `(0,1]`. -/
theorem exists_smoothWeight_gradient_bound :
    ∃ G > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x,
      cutoffGradientSq (χ.smoothWeight ε) x ≤ G := by
  obtain ⟨Bp, hBp, hbp⟩ := exists_cutoff_smoothPositivePart_fderiv_bound
    χ.plus_smooth χ.plus_compact χ.plus_range (normalCoordinate_contDiff p)
  obtain ⟨Bm, hBm, hbm⟩ := exists_cutoff_smoothPositivePart_fderiv_bound
    χ.minus_smooth χ.minus_compact χ.minus_range
    ((normalCoordinate_contDiff p).comp reflection_contDiff)
  refine ⟨2 * (Bp + Bm) ^ 2, by positivity, ?_⟩
  intro ε hε hε1 x
  have hp : DifferentiableAt ℝ (fun y => χ.plus y * smoothPositivePart ε (p.normalCoordinate y)) x :=
    (χ.plus_smooth.mul ((smoothPositivePart_contDiff hε).comp
      (normalCoordinate_contDiff p))).differentiable (by simp) x
  have hm : DifferentiableAt ℝ
      (fun y => χ.minus y * smoothPositivePart ε (p.normalCoordinate (reflection y))) x :=
    (χ.minus_smooth.mul ((smoothPositivePart_contDiff hε).comp
      ((normalCoordinate_contDiff p).comp reflection_contDiff))).differentiable (by simp) x
  have hn : ‖fderiv ℝ (χ.smoothWeight ε) x‖ ≤ Bp + Bm := by
    change ‖fderiv ℝ (fun y => χ.plus y * smoothPositivePart ε (p.normalCoordinate y) +
      χ.minus y * smoothPositivePart ε (p.normalCoordinate (reflection y))) x‖ ≤ _
    rw [fderiv_fun_add hp hm]
    exact (norm_add_le _ _).trans (add_le_add (hbp ε hε hε1 x) (hbm ε hε hε1 x))
  have hpartial (i : Fin 2) : |realPartialDerivative i (χ.smoothWeight ε) x| ≤ Bp + Bm := by
    calc
      _ = ‖fderiv ℝ (χ.smoothWeight ε) x (coordinateVector i)‖ := rfl
      _ ≤ ‖fderiv ℝ (χ.smoothWeight ε) x‖ * ‖coordinateVector i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ Bp + Bm := by
        have hi : ‖coordinateVector i‖ = 1 := by simp [coordinateVector]
        rwa [hi, mul_one]
  have hs (i : Fin 2) : realPartialDerivative i (χ.smoothWeight ε) x ^ 2 ≤ (Bp + Bm) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (add_nonneg hBp.le hBm.le)).mpr (hpartial i)
    simpa only [sq_abs] using h
  simpa only [cutoffGradientSq, Fin.sum_univ_two, two_mul] using add_le_add (hs 0) (hs 1)

theorem exists_smoothWeight_uniform_bounds :
    ∃ M > 0, ∃ G > 0, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ x,
      χ.smoothWeight ε x ∈ Icc 0 M ∧ cutoffGradientSq (χ.smoothWeight ε) x ≤ G := by
  obtain ⟨M, hM, hb⟩ := χ.exists_smoothWeight_bound
  obtain ⟨G, hG, hg⟩ := χ.exists_smoothWeight_gradient_bound
  exact ⟨M, hM, G, hG, fun ε hε x => ⟨hb ε hε.1 hε.2 x, hg ε hε.1 hε.2 x⟩⟩

end CuspParameters.CuspWeightCutoffs
end InfiniteZero
