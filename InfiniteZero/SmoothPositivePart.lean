import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A smooth approximation of the positive part

For positive smoothing parameter the approximation is smooth, nonnegative
and has derivative between zero and one. Its uniform error on the whole real
line is at most half the parameter. No spatial or spectral assumptions enter
these scalar estimates.
-/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace InfiniteZero

def smoothPositivePart (ε t : ℝ) : ℝ :=
  (t + Real.sqrt (t ^ 2 + ε ^ 2)) / 2

private theorem abs_le_sqrt_sq_add_sq (ε t : ℝ) :
    |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) := by
  have h := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε) :
    t ^ 2 ≤ t ^ 2 + ε ^ 2)
  simpa only [Real.sqrt_sq_eq_abs] using h

theorem smoothPositivePart_nonneg (ε t : ℝ) : 0 ≤ smoothPositivePart ε t := by
  have h := abs_le_sqrt_sq_add_sq ε t
  have ht := neg_le_abs t
  unfold smoothPositivePart
  linarith only [h, ht]

theorem smoothPositivePart_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (smoothPositivePart ε) := by
  exact (contDiff_id.add (((contDiff_id.pow 2).add contDiff_const).sqrt
    (fun t => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t)
      (sq_pos_of_pos hε))))).div_const 2

/-- A signed error bound, stronger than the absolute approximation estimate. -/
theorem smoothPositivePart_sub_max_bounds {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ smoothPositivePart ε t - max t 0 ∧
      smoothPositivePart ε t - max t 0 ≤ ε / 2 := by
  have hlo := abs_le_sqrt_sq_add_sq ε t
  have hhi : Real.sqrt (t ^ 2 + ε ^ 2) ≤ |t| + ε := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (abs_nonneg t) hε, ?_⟩
    nlinarith only [sq_abs t, mul_nonneg (abs_nonneg t) hε]
  have heq : smoothPositivePart ε t - max t 0 =
      (Real.sqrt (t ^ 2 + ε ^ 2) - |t|) / 2 := by
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, abs_of_nonneg ht]
      unfold smoothPositivePart
      ring
    · rw [max_eq_right ht, abs_of_nonpos ht]
      unfold smoothPositivePart
      ring
  rw [heq]
  constructor <;> linarith only [hlo, hhi]

theorem smoothPositivePart_abs_sub_max_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    |smoothPositivePart ε t - max t 0| ≤ ε / 2 := by
  obtain ⟨hlo, hhi⟩ := smoothPositivePart_sub_max_bounds hε t
  rwa [abs_of_nonneg hlo]

theorem hasDerivAt_smoothPositivePart {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (smoothPositivePart ε)
      ((1 + t / Real.sqrt (t ^ 2 + ε ^ 2)) / 2) t := by
  have hs : t ^ 2 + ε ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hε))
  have hd := ((hasDerivAt_id t).add
    ((((hasDerivAt_id t).pow 2).add_const (ε ^ 2)).sqrt hs)).div_const 2
  convert hd using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub,
    Pi.pow_apply, id_eq, pow_one, mul_one]
  ring

theorem deriv_smoothPositivePart {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (smoothPositivePart ε) t =
      (1 + t / Real.sqrt (t ^ 2 + ε ^ 2)) / 2 :=
  (hasDerivAt_smoothPositivePart hε t).deriv

theorem deriv_smoothPositivePart_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (smoothPositivePart ε) t ∧ deriv (smoothPositivePart ε) t ≤ 1 := by
  have hs : 0 < Real.sqrt (t ^ 2 + ε ^ 2) :=
    Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hε))
  have hb := abs_le.mp (abs_le_sqrt_sq_add_sq ε t)
  have hlo : -1 ≤ t / Real.sqrt (t ^ 2 + ε ^ 2) :=
    (le_div_iff₀ hs).mpr (by simpa only [neg_one_mul] using hb.1)
  have hhi : t / Real.sqrt (t ^ 2 + ε ^ 2) ≤ 1 :=
    (div_le_iff₀ hs).mpr (by simpa only [one_mul] using hb.2)
  rw [deriv_smoothPositivePart hε t]
  constructor <;> linarith only [hlo, hhi]

theorem smoothPositivePart_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (smoothPositivePart ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (hasDerivAt_smoothPositivePart hε t).differentiableAt)
  intro t
  have hb := deriv_smoothPositivePart_bounds hε t
  change ‖deriv (smoothPositivePart ε) t‖ ≤ (1 : ℝ)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

/-- Uniform convergence on the entire real line as the positive smoothing
parameter tends to zero. -/
theorem tendstoUniformly_smoothPositivePart :
    TendstoUniformly smoothPositivePart (fun t : ℝ => max t 0) (𝓝[>] (0 : ℝ)) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 2 * δ :=
    (eventually_lt_nhds (show (0 : ℝ) < 2 * δ by positivity)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmall
  intro t
  rw [Real.dist_eq, abs_sub_comm]
  exact (smoothPositivePart_abs_sub_max_le (le_of_lt hε) t).trans_lt (by linarith)

end InfiniteZero
