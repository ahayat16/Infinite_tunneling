import InfiniteZero.MagneticWeightedGraph
import InfiniteZero.EigenfunctionCutoffLimits

/-!
# Strong limits and norm lower bounds for the actual L² multipliers

Uniformly bounded continuous real multipliers converge strongly whenever
their scalar functions converge pointwise. The proof uses dominated
convergence of the mass of the difference and keeps all representatives
identified almost everywhere. No derivative convergence is required.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace InfiniteZero

/-- Pointwise convergence with fixed scalar bounds gives strong convergence
of the concrete multiplication operators on every L² vector. -/
theorem tendsto_boundedPotentialMul_apply (Wn : ℕ → Potential) (W : Potential)
    (hWn : ∀ n, Continuous (Wn n)) (hW : Continuous W) {C D : ℝ}
    (hboundn : ∀ n x, |Wn n x| ≤ C) (hbound : ∀ x, |W x| ≤ D)
    (hlim : ∀ x, Tendsto (fun n => Wn n x) atTop (𝓝 (W x))) (u : L2Space) :
    Tendsto (fun n => boundedPotentialMul (Wn n) (hWn n) (hboundn n) u) atTop
      (𝓝 (boundedPotentialMul W hW hbound u)) := by
  let Mn : ℕ → L2Space →L[ℂ] L2Space :=
    fun n => boundedPotentialMul (Wn n) (hWn n) (hboundn n)
  let M : L2Space →L[ℂ] L2Space := boundedPotentialMul W hW hbound
  have hdiffbound : ∀ n x, |Wn n x - W x| ≤ C + D := fun n x =>
    (abs_sub _ _).trans (add_le_add (hboundn n x) (hbound x))
  have hdiff : ∀ x, Tendsto (fun n => Wn n x - W x) atTop (𝓝 (0 : ℝ)) := by
    intro x
    simpa only [sub_self] using (hlim x).sub_const (W x)
  have hm := tendsto_mass_real_cutoff_of_bounded (Lp.memLp u)
    (c := fun n x => Wn n x - W x) (cLimit := fun _ => 0)
    (fun n => ((hWn n).sub hW).measurable) hdiffbound hdiff
  have hzero : mass (fun x : Plane => ((0 : ℝ) : ℂ) * u x) = 0 := by
    simp [mass]
  rw [hzero] at hm
  have hrep (n : ℕ) : Represents (Mn n u - M u)
      (fun x => ((Wn n x - W x : ℝ) : ℂ) * u x) := by
    filter_upwards [Lp.coeFn_sub (Mn n u) (M u),
      coe_boundedPotentialMul (Wn n) (hWn n) (hboundn n) u,
      coe_boundedPotentialMul W hW hbound u] with x hx hn hWux
    change (Mn n u - M u) x = _
    calc
      _ = (Mn n u) x - (M u) x := hx
      _ = _ := by
        rw [hn, hWux, Complex.ofReal_sub, sub_mul]
  have hsq : Tendsto (fun n => ‖Mn n u - M u‖ ^ 2) atTop (𝓝 (0 : ℝ)) :=
    hm.congr' (Eventually.of_forall fun n => (hrep n).norm_sq_eq_mass.symm)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

/-- A real weight at least one expands the L² norm. This does not require
any preservation of a differential operator domain. -/
theorem norm_lower_boundedPotentialMul (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) (hWone : ∀ x, 1 ≤ W x) (u : L2Space) :
    ‖u‖ ≤ ‖boundedPotentialMul W hW hbound u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coe_boundedPotentialMul W hW hbound u] with x hx
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans (hWone x))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hWone x) (norm_nonneg (u x))

end InfiniteZero
