import InfiniteZero.MagneticModel
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Quantitative radial composition on a fixed planar annulus

The radius map is smooth away from zero. Its jets on a fixed closed annulus
are uniformly bounded independently of the scalar profile to be composed.
This transports radial derivative estimates to physical Fréchet derivatives
without changing their exponential envelope.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

theorem exists_norm_jet_bound_on_annulus {rMin rMax : ℝ} (hMin : 0 < rMin) (n : ℕ) :
    ∃ C > 0, ∀ x : Plane, ‖x‖ ∈ Icc rMin rMax →
      ‖iteratedFDeriv ℝ n (fun y : Plane => ‖y‖) x‖ ≤ C := by
  let S : Set Plane := {x | ‖x‖ ∈ Icc rMin rMax}
  have hS : IsCompact S := by
    have heq : S = Metric.closedBall (0 : Plane) rMax \ Metric.ball 0 rMin := by
      ext x
      simp only [S, mem_setOf_eq, mem_Icc, mem_diff, Metric.mem_closedBall,
        Metric.mem_ball, dist_zero_right, not_lt]
      tauto
    rw [heq]
    exact (isCompact_closedBall (0 : Plane) rMax).diff Metric.isOpen_ball
  have hc : ContinuousOn (iteratedFDeriv ℝ n (fun y : Plane => ‖y‖)) S := by
    intro x hx
    have hxpos : 0 < ‖x‖ := hMin.trans_le hx.1
    exact ((contDiffAt_norm ℝ (norm_pos_iff.mp hxpos) :
      ContDiffAt ℝ n (fun y : Plane => ‖y‖) x).continuousAt_iteratedFDeriv
        le_rfl).continuousWithinAt
  obtain ⟨C, hC, hb⟩ := (hS.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun x hx => hb _ ⟨x, hx, rfl⟩⟩

/-- One number bounds all the positive-order radius jets up to the fixed
order by its corresponding powers. -/
theorem exists_norm_jets_power_bound_on_annulus {rMin rMax : ℝ}
    (hMin : 0 < rMin) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : Plane, ‖x‖ ∈ Icc rMin rMax →
      ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun y : Plane => ‖y‖) x‖ ≤ D ^ i := by
  choose C hC hb using fun i : ℕ => exists_norm_jet_bound_on_annulus
    (rMax := rMax) hMin i
  let D := 1 + ∑ i ∈ Finset.range (n + 1), C i
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), C i :=
    Finset.sum_nonneg (fun i _ => (hC i).le)
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro x hx i hi hin
  have hiSum : C i ≤ ∑ j ∈ Finset.range (n + 1), C j :=
    Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_range.mpr (by omega))
  have hiD : C i ≤ D := by dsimp [D]; linarith
  exact (hb i x hx).trans (hiD.trans (le_self_pow₀ hD (by omega)))

/-- The constant depends only on the annulus and the order, and is fixed
before the scalar profile, its bound and the evaluation point. -/
theorem exists_radial_composition_jet_bound {rMin rMax : ℝ}
    (hMin : 0 < rMin) (n : ℕ) :
    ∃ C > 0, ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f (Ioi 0) →
      ∀ x : Plane, ‖x‖ ∈ Icc rMin rMax → ∀ B : ℝ, 0 ≤ B →
        (∀ i : ℕ, i ≤ n → ‖iteratedDeriv i f ‖x‖‖ ≤ B) →
        ‖iteratedFDeriv ℝ n (fun y : Plane => f ‖y‖) x‖ ≤ C * B := by
  obtain ⟨D, hD, hnorm⟩ := exists_norm_jets_power_bound_on_annulus (rMax := rMax) hMin n
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hnfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  refine ⟨(n.factorial : ℝ) * D ^ n, by positivity, ?_⟩
  intro f hf x hx B _hB hB
  let S : Set Plane := {0}ᶜ
  have hs : IsOpen S := isClosed_singleton.isOpen_compl
  have hxpos : 0 < ‖x‖ := hMin.trans_le hx.1
  have hxS : x ∈ S := norm_pos_iff.mp hxpos
  have hnormSmooth : ContDiffOn ℝ n (fun y : Plane => ‖y‖) S := by
    intro y hy
    exact (contDiffAt_norm ℝ (show y ≠ 0 from hy)).contDiffWithinAt
  have hmaps : MapsTo (fun y : Plane => ‖y‖) S (Ioi 0) := by
    intro y hy
    exact norm_pos_iff.mpr (show y ≠ 0 from hy)
  have hscalar : ∀ i : ℕ, i ≤ n →
      ‖iteratedFDerivWithin ℝ i f (Ioi 0) ‖x‖‖ ≤ B := by
    intro i hi
    rw [(iteratedFDerivWithin_of_isOpen i isOpen_Ioi) hxpos,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hB i hi
  have hradius : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : Plane => ‖y‖) S x‖ ≤ D ^ i := by
    intro i hi hin
    rw [(iteratedFDerivWithin_of_isOpen i hs) hxS]
    exact hnorm x hx i hi hin
  have hcomp := norm_iteratedFDerivWithin_comp_le (contDiffOn_infty.mp hf n) hnormSmooth
    le_rfl
    isOpen_Ioi.uniqueDiffOn hs.uniqueDiffOn
    hmaps hxS hscalar hradius
  rw [(iteratedFDerivWithin_of_isOpen n hs) hxS] at hcomp
  simpa only [Function.comp_def, mul_right_comm] using hcomp

end InfiniteZero
