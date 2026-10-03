import InfiniteZero.MagneticAffineRescaling
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform coefficient bounds for magnetic rescaling

All constants precede the scale, the centre and the scaled energy. Smoothness
of the physical potential suffices: the rescaled ball only visits a fixed
compact subset of the physical plane.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

theorem contDiff_rescaledMagneticFirstOrder (b : ℝ) (x₀ : Plane) (h : ℝ)
    (i : Fin 2) : ContDiff ℝ ∞ (rescaledMagneticFirstOrder b x₀ h i) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((contDiff_perpCoordinate i).comp (contDiff_affineScale x₀ h)))

theorem contDiff_rescaledMagneticZerothOrder (b : ℝ) {V : Potential}
    (hV : ContDiff ℝ ∞ V) (e : ℝ) (x₀ : Plane) (h : ℝ) :
    ContDiff ℝ ∞ (rescaledMagneticZerothOrder b V e x₀ h) :=
  Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_affineScale x₀ h))).add
      (hV.comp (contDiff_affineScale x₀ h))).sub contDiff_const)

/-- Every finite family of jets of a smooth function is bounded on a closed
ball. No compact-support assumption on the function is needed. -/
theorem exists_smooth_jet_bound_closedBall {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) (R : ℝ) (n : ℕ) :
    ∃ C > 0, ∀ x : Plane, ‖x‖ ≤ R → ∀ j : ℕ, j ≤ n →
      ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hone (j : ℕ) : ∃ C > 0, ∀ x : Plane, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ j f) :=
      hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨C, hC, hbound⟩ :=
      ((isCompact_closedBall (0 : Plane) R).image hc).isBounded.exists_pos_norm_le
    refine ⟨C, hC, fun x hx => hbound _ ?_⟩
    exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩
  choose C hC hbound using hone
  let B := 1 + ∑ j ∈ Finset.range (n + 1), C j
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), C j :=
    Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro x hx j hj
  have hjSum : C j ≤ ∑ k ∈ Finset.range (n + 1), C k :=
    Finset.single_le_sum (fun k _ => (hC k).le) (Finset.mem_range.mpr (by omega))
  exact (hbound j x hx).trans (by dsimp [B]; linarith)

/-- Pulling a smooth physical function back to the fixed ball of radius two
preserves a uniform bound on any fixed finite family of jets. -/
theorem exists_affineScale_jet_bound {f : Wavefunction} (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (n : ℕ) :
    ∃ C > 0, ∀ h ∈ Icc (0 : ℝ) 1, ∀ x₀ : Plane, ‖x₀‖ ≤ R →
      ∀ j : ℕ, j ≤ n → ∀ y ∈ Metric.closedBall (0 : Plane) 2,
        ‖iteratedFDeriv ℝ j (f ∘ affineScale x₀ h) y‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_smooth_jet_bound_closedBall hf (R + 2) n
  refine ⟨C, hC, ?_⟩
  intro h hh x₀ hx₀ j hj y hy
  have hy' : ‖y‖ ≤ 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hxy : ‖affineScale x₀ h y‖ ≤ R + 2 := by
    calc
      ‖affineScale x₀ h y‖ ≤ ‖x₀‖ + ‖h • y‖ := norm_add_le _ _
      _ = ‖x₀‖ + h * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh.1]
      _ ≤ ‖x₀‖ + ‖y‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hh.2 (norm_nonneg y)]
      _ ≤ R + 2 := add_le_add hx₀ hy'
  rw [norm_iteratedFDeriv_affineScale_of_nonneg hf x₀ hh.1]
  calc
    h ^ j * ‖iteratedFDeriv ℝ j f (affineScale x₀ h y)‖ ≤
        1 * ‖iteratedFDeriv ℝ j f (affineScale x₀ h y)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hh.1 hh.2) (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hbound _ hxy j hj

private theorem norm_iteratedFDeriv_constant_le (c : ℂ) (j : ℕ) (y : Plane) :
    ‖iteratedFDeriv ℝ j (fun _ : Plane => c) y‖ ≤ ‖c‖ := by
  cases j with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity

/-- The coefficient bound is chosen before the scale, the centre and the
scaled energy, and holds simultaneously for every derivative order up to n.
The closed ball and the endpoint h=0 are included in this stronger version. -/
theorem exists_rescaledMagneticCoefficient_jet_bound (b : ℝ) (V : Potential)
    (hV : ContDiff ℝ ∞ V) (n : ℕ) (R Benergy : ℝ) :
    ∃ B > 0, ∀ h ∈ Icc (0 : ℝ) 1, ∀ x₀ : Plane, ‖x₀‖ ≤ R →
      ∀ e : ℝ, |e| ≤ Benergy → ∀ j : ℕ, j ≤ n →
      ∀ y ∈ Metric.closedBall (0 : Plane) 2,
        (∀ i : Fin 2,
          ‖iteratedFDeriv ℝ j (rescaledMagneticFirstOrder b x₀ h i) y‖ ≤ B) ∧
        ‖iteratedFDeriv ℝ j (rescaledMagneticZerothOrder b V e x₀ h) y‖ ≤ B := by
  let a : Fin 2 → Wavefunction := fun i x =>
    Complex.I * (b : ℂ) * (perpCoordinate x i : ℂ)
  have ha (i : Fin 2) : ContDiff ℝ ∞ (a i) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_perpCoordinate i))
  let q : Wavefunction := fun x => (((b / 2) ^ 2 * ‖x‖ ^ 2 + V x : ℝ) : ℂ)
  have hq : ContDiff ℝ ∞ q :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul (contDiff_norm_sq ℝ)).add hV)
  choose A hA hAbound using fun i => exists_affineScale_jet_bound (ha i) R n
  obtain ⟨Q, hQ, hQbound⟩ := exists_affineScale_jet_bound hq R n
  let B := (∑ i : Fin 2, A i) + Q + |Benergy| + 1
  have hsum : 0 ≤ ∑ i : Fin 2, A i := Finset.sum_nonneg (fun i _ => (hA i).le)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro h hh x₀ hx₀ e he j hj y hy
  constructor
  · intro i
    have hi := hAbound i h hh x₀ hx₀ j hj y hy
    have hiSum : A i ≤ ∑ k : Fin 2, A k :=
      Finset.single_le_sum (fun k _ => (hA k).le) (Finset.mem_univ i)
    change ‖iteratedFDeriv ℝ j (a i ∘ affineScale x₀ h) y‖ ≤ B
    exact hi.trans (by dsimp [B]; linarith [abs_nonneg Benergy])
  · have he' : |e| ≤ |Benergy| := he.trans (le_abs_self Benergy)
    have heq : rescaledMagneticZerothOrder b V e x₀ h =
        (q ∘ affineScale x₀ h) - (fun _ : Plane => (e : ℂ)) := by
      funext z
      simp only [rescaledMagneticZerothOrder, q, Function.comp_apply, Pi.sub_apply,
        Complex.ofReal_sub]
    rw [heq, iteratedFDeriv_sub_apply
      ((hq.comp (contDiff_affineScale x₀ h)).of_le (by exact_mod_cast le_top)).contDiffAt
      contDiffAt_const]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (q ∘ affineScale x₀ h) y‖ +
          ‖iteratedFDeriv ℝ j (fun _ : Plane => (e : ℂ)) y‖ := norm_sub_le _ _
      _ ≤ Q + ‖(e : ℂ)‖ := add_le_add (hQbound h hh x₀ hx₀ j hj y hy)
        (norm_iteratedFDeriv_constant_le (e : ℂ) j y)
      _ ≤ B := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        dsimp [B]
        linarith

end InfiniteZero
