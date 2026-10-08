import InfiniteZero.EllipticInteriorContract
import InfiniteZero.MagneticLocalEnergy
import InfiniteZero.MagneticEllipticExpansion
import InfiniteZero.SmoothExhaustionCutoffs
import InfiniteZero.WeightedLocalMassComparison
import Mathlib.Tactic.GCongr

/-!
# A local energy estimate with complex lower-order coefficients

The cutoff identity for the Laplacian and Young's inequality give a
uniform local gradient bound. Only the values of the lower-order
coefficients are bounded; no derivative or sign assumption is used.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
namespace InfiniteZero

/-- A cutoff for two prescribed concentric balls, with a finite gradient
bound chosen before any coefficients or solution. -/
theorem exists_elliptic_cutoff {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ χ : Plane → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Metric.closedBall (0 : Plane) r, χ x = 1) ∧
      tsupport χ ⊆ Metric.ball (0 : Plane) R ∧
      ∃ D ≥ 0, ∀ x, cutoffGradientSq χ x ≤ D := by
  let χ : ContDiffBump (0 : Plane) :=
    { rIn := r, rOut := (r + R) / 2, rIn_pos := hr, rIn_lt_rOut := by linarith }
  have hχ : ContDiff ℝ ∞ (χ : Plane → ℝ) := χ.contDiff
  have hc : HasCompactSupport (χ : Plane → ℝ) := χ.hasCompactSupport
  obtain ⟨B, hB, hb⟩ := ((hc.fderiv ℝ).isCompact_range
    (hχ.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨χ, hχ, hc, fun _ => ⟨χ.nonneg, χ.le_one⟩,
    fun x hx => χ.one_of_mem_closedBall hx, ?_, 2 * B ^ 2, by positivity, ?_⟩
  · rw [χ.tsupport_eq]
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have hx' := Metric.mem_closedBall.mp hx
    simp only [dist_zero_right] at hx'
    change ‖x‖ ≤ (r + R) / 2 at hx'
    linarith
  · intro x
    have hp (i : Fin 2) : |realPartialDerivative i χ x| ≤ B := by
      calc
        _ = ‖fderiv ℝ (χ : Plane → ℝ) x (coordinateVector i)‖ := rfl
        _ ≤ ‖fderiv ℝ (χ : Plane → ℝ) x‖ * ‖coordinateVector i‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (χ : Plane → ℝ) x‖ := by simp [coordinateVector]
        _ ≤ B := hb _ ⟨x, rfl⟩
    have hs (i : Fin 2) : realPartialDerivative i χ x ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB.le).mpr (hp i)
    simpa [cutoffGradientSq, Fin.sum_univ_two, two_mul] using add_le_add (hs 0) (hs 1)

/-- The zero-field magnetic form is the ordinary Dirichlet energy. -/
theorem magneticForm_zero_eq_gradient (u : Wavefunction) :
    magneticForm 0 0 (fun _ => 0) u =
      ∫ x : Plane, ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2 := by
  simp [magneticForm, covariantDerivative]

/-- A component of the lower-order drift can be absorbed into the
gradient of the cutoff solution. -/
private theorem cutoff_drift_bound {B c : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c)
    {a z v : ℂ} (ha : ‖a‖ ≤ B) (d : ℝ) :
    ‖star (((c ^ 2 : ℝ) : ℂ) * z) * (a * v)‖ ≤
      (1 / 4 : ℝ) * ‖(c : ℂ) * v + (d : ℂ) * z‖ ^ 2 +
        (3 / 2 * B ^ 2 * c ^ 2 + 1 / 2 * d ^ 2) * ‖z‖ ^ 2 := by
  let t := ‖(c : ℂ) * v + (d : ℂ) * z‖
  have hv : c * ‖v‖ ≤ t + |d| * ‖z‖ := by
    calc
      _ = ‖(c : ℂ) * v‖ := by simp [abs_of_nonneg hc]
      _ = ‖((c : ℂ) * v + (d : ℂ) * z) - (d : ℂ) * z‖ := by congr 1; ring
      _ ≤ _ := by simpa [t, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_sub_le ((c : ℂ) * v + (d : ℂ) * z) ((d : ℂ) * z)
  have hmul : c ^ 2 * ‖z‖ * ‖a‖ * ‖v‖ ≤
      B * c * ‖z‖ * (t + |d| * ‖z‖) := by
    calc
      _ ≤ c ^ 2 * ‖z‖ * B * ‖v‖ := by gcongr
      _ = B * c * ‖z‖ * (c * ‖v‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  have hy₁ := sq_nonneg (t / 2 - B * c * ‖z‖)
  have hy₂ := mul_nonneg (sq_nonneg (B * c - |d|)) (sq_nonneg ‖z‖)
  have hd : |d| ^ 2 = d ^ 2 := sq_abs d
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg c)]
  dsimp [t] at hmul hy₁ ⊢
  nlinarith

private theorem cutoff_density_bound {B D c : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (a v : Fin 2 → ℂ) (d : Fin 2 → ℝ)
    {q z f : ℂ} (ha : ∀ i, ‖a i‖ ≤ B) (hq : ‖q‖ ≤ B)
    (hd : ∑ i, d i ^ 2 ≤ D) :
    (star (((c ^ 2 : ℝ) : ℂ) * z) * (f - (∑ i, a i * v i) - q * z)).re +
        (∑ i, d i ^ 2) * ‖z‖ ^ 2 ≤
      (1 / 2 : ℝ) * (∑ i, ‖(c : ℂ) * v i + (d i : ℂ) * z‖ ^ 2) +
        (4 * B ^ 2 + 2 * B + 2 + 4 * D) * (‖z‖ ^ 2 + ‖f‖ ^ 2) := by
  have hsplit : star (((c ^ 2 : ℝ) : ℂ) * z) *
      (f - (∑ i, a i * v i) - q * z) =
      star (((c ^ 2 : ℝ) : ℂ) * z) * f -
        (∑ i, star (((c ^ 2 : ℝ) : ℂ) * z) * (a i * v i)) -
        star (((c ^ 2 : ℝ) : ℂ) * z) * (q * z) := by
    simp only [Fin.sum_univ_two]
    ring
  have hre : (star (((c ^ 2 : ℝ) : ℂ) * z) *
      (f - (∑ i, a i * v i) - q * z)).re ≤
      ‖star (((c ^ 2 : ℝ) : ℂ) * z) * f‖ +
        (∑ i, ‖star (((c ^ 2 : ℝ) : ℂ) * z) * (a i * v i)‖) +
        ‖star (((c ^ 2 : ℝ) : ℂ) * z) * (q * z)‖ := by
    rw [hsplit]
    exact (Complex.re_le_norm _).trans
      (((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
        (add_le_add (add_le_add le_rfl (norm_sum_le _ _)) le_rfl))
  have hs : ‖star (((c ^ 2 : ℝ) : ℂ) * z) * f‖ ≤
      (c ^ 2 / 2) * (‖z‖ ^ 2 + ‖f‖ ^ 2) := by
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg c)]
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (‖z‖ - ‖f‖))]
  have hq' : ‖star (((c ^ 2 : ℝ) : ℂ) * z) * (q * z)‖ ≤
      B * c ^ 2 * ‖z‖ ^ 2 := by
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg c)]
    calc
      _ ≤ c ^ 2 * ‖z‖ * (B * ‖z‖) := by gcongr
      _ = _ := by ring
  have h₀ := cutoff_drift_bound hB hc (ha 0) (d 0) (z := z) (v := v 0)
  have h₁ := cutoff_drift_bound hB hc (ha 1) (d 1) (z := z) (v := v 1)
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hcz : c ^ 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  have hcf : c ^ 2 * ‖f‖ ^ 2 ≤ ‖f‖ ^ 2 := by nlinarith [sq_nonneg ‖f‖]
  have hcB := mul_le_mul_of_nonneg_left hcz (show 0 ≤ 3 * B ^ 2 + B + 1 by positivity)
  have hdz := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖z‖)
  have hfB := mul_nonneg (show 0 ≤ 4 * B ^ 2 + 2 * B + 1 + 4 * D by positivity)
    (sq_nonneg ‖f‖)
  simp only [Fin.sum_univ_two] at hre hd hdz ⊢
  nlinarith [sq_nonneg ‖(c : ℂ) * v 0 + (d 0 : ℂ) * z‖,
    sq_nonneg ‖(c : ℂ) * v 1 + (d 1 : ℂ) * z‖,
    mul_nonneg (sq_nonneg B) (sq_nonneg ‖z‖),
    mul_nonneg hB (sq_nonneg ‖z‖), mul_nonneg hD (sq_nonneg ‖z‖), sq_nonneg ‖z‖]

/-- Uniform local gradient estimate for a smooth solution with bounded
complex lower-order coefficients. The radii and bound precede all data. -/
theorem exists_elliptic_local_gradient_bound {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (a : Fin 2 → Wavefunction) (q u f : Wavefunction),
      ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
      (∀ x ∈ Metric.ball (0 : Plane) R, (∀ i, ‖a i x‖ ≤ B) ∧ ‖q x‖ ≤ B) →
      (∀ x ∈ Metric.ball (0 : Plane) R, ellipticExpression a q u x = f x) →
      (∫ x in Metric.ball (0 : Plane) r,
        ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) ≤
        C * ((∫ x in Metric.ball (0 : Plane) R, ‖u x‖ ^ 2) +
          ∫ x in Metric.ball (0 : Plane) R, ‖f x‖ ^ 2) := by
  obtain ⟨χ, hχ, hc, hχ01, hχone, hsupp, D, hD, hgrad⟩ :=
    exists_elliptic_cutoff hr hrR
  let K := 4 * B ^ 2 + 2 * B + 2 + 4 * D
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2 * K, by positivity, ?_⟩
  intro a q u f hu hf hcoeff heq
  let ψ : Wavefunction := fun x => (χ x : ℂ) * u x
  let g : Plane → ℝ := fun x => ∑ i : Fin 2, ‖partialDerivative i ψ x‖ ^ 2
  let lap : Wavefunction := fun x => -(∑ i : Fin 2, partialDerivative i (partialDerivative i u) x)
  let density : Plane → ℝ := fun x =>
    (star (((χ x ^ 2 : ℝ) : ℂ) * u x) * lap x).re + cutoffGradientSq χ x * ‖u x‖ ^ 2
  have hψ : IsTestFunction ψ := isTestFunction_compact_real_mul hχ hc hu
  have hψsq : IsTestFunction (fun x => ((χ x ^ 2 : ℝ) : ℂ) * u x) :=
    isTestFunction_compact_real_mul (hχ.pow 2)
      (hc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)) hu
  have hlap : Continuous lap := by
    exact (continuous_finsetSum _ fun i _ =>
      (contDiff_partialDerivative i (contDiff_partialDerivative i hu)).continuous).neg
  have hidensity : Integrable density :=
    (hψsq.integrable_star_mul hlap).re.add (integrable_cutoffGradientSq_mul hχ hc hu.continuous)
  have hg : Integrable g :=
    integrable_finsetSum Finset.univ fun i _ => (hψ.partialDerivative i).integrable_norm_sq
  have hψsupp : tsupport ψ ⊆ Metric.ball (0 : Plane) R := by
    exact (tsupport_mul_subset_left.trans
      (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) (by simp) χ)).trans hsupp
  have hgzero (x : Plane) (hx : x ∉ Metric.ball (0 : Plane) R) : g x = 0 := by
    have hn : x ∉ tsupport ψ := fun hx' => hx (hψsupp hx')
    simp [g, partialDerivative, fderiv_of_notMem_tsupport ℝ hn]
  have hdzero (x : Plane) (hx : x ∉ Metric.ball (0 : Plane) R) : density x = 0 := by
    have hn : x ∉ tsupport χ := fun hx' => hx (hsupp hx')
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport hn
    simp [density, hz, cutoffGradientSq, realPartialDerivative, fderiv_of_notMem_tsupport ℝ hn]
  have hham (x : Plane) : magneticHamiltonian 0 0 (fun _ => 0) u x = lap x := by
    simpa [lap] using magneticHamiltonian_expansion 0 0 (fun _ => 0) hu x
  have henergy : (∫ x in Metric.ball (0 : Plane) R, g x) =
      ∫ x in Metric.ball (0 : Plane) R, density x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgzero,
      setIntegral_eq_integral_of_forall_compl_eq_zero hdzero]
    calc
      _ = magneticForm 0 0 (fun _ => 0) ψ := (magneticForm_zero_eq_gradient ψ).symm
      _ = (waveInner (fun x => ((χ x ^ 2 : ℝ) : ℂ) * u x) lap).re +
          ∫ x : Plane, cutoffGradientSq χ x * ‖u x‖ ^ 2 := by
        rw [magneticForm_cutoff 0 0 continuous_const hχ hc hu]
        rw [show magneticHamiltonian 0 0 (fun _ => 0) u = lap from funext hham]
      _ = _ := by
        rw [show waveInner (fun x => ((χ x ^ 2 : ℝ) : ℂ) * u x) lap =
          ∫ x, star (((χ x ^ 2 : ℝ) : ℂ) * u x) * lap x from rfl]
        dsimp only [density]
        have hir : Integrable (fun x => (star (((χ x ^ 2 : ℝ) : ℂ) * u x) * lap x).re) :=
          (hψsq.integrable_star_mul hlap).re
        rw [integral_add hir
          (integrable_cutoffGradientSq_mul hχ hc hu.continuous)]
        congr 1
        exact (integral_re (hψsq.integrable_star_mul hlap)).symm
  have hpoint (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) R) :
      density x ≤ (1 / 2 : ℝ) * g x + K * (‖u x‖ ^ 2 + ‖f x‖ ^ 2) := by
    have hl : lap x = f x - (∑ i, a i x * partialDerivative i u x) - q x * u x := by
      have he := heq x hx
      change lap x + (∑ i, a i x * partialDerivative i u x) + q x * u x = f x at he
      linear_combination he
    have hv (i : Fin 2) : partialDerivative i ψ x =
        (χ x : ℂ) * partialDerivative i u x + (realPartialDerivative i χ x : ℂ) * u x :=
      partialDerivative_real_mul i (hχ.differentiable (by simp) x) (hu.differentiable (by simp) x)
    dsimp only [density, g]
    rw [hl]
    simp_rw [hv]
    exact cutoff_density_bound hB hD (hχ01 x).1 (hχ01 x).2
      (fun i => a i x) (fun i => partialDerivative i u x) (fun i => realPartialDerivative i χ x)
      (hcoeff x hx).1 (hcoeff x hx).2 (hgrad x)
  have hiu := continuous_integrableOn_norm_sq_ball hu.continuous (0 : Plane) R
  have hif := continuous_integrableOn_norm_sq_ball hf.continuous (0 : Plane) R
  have hint := setIntegral_mono_on hidensity.integrableOn
    ((hg.integrableOn.const_mul (1 / 2 : ℝ)).add ((hiu.add hif).const_mul K))
    measurableSet_ball hpoint
  simp only [Pi.add_apply] at hint
  rw [← henergy] at hint
  have hhalf : IntegrableOn (fun x => (1 / 2 : ℝ) * g x)
      (Metric.ball (0 : Plane) R) volume := hg.integrableOn.const_mul (1 / 2 : ℝ)
  have hdata : IntegrableOn (fun x => K * (‖u x‖ ^ 2 + ‖f x‖ ^ 2))
      (Metric.ball (0 : Plane) R) volume := (hiu.add hif).const_mul K
  rw [integral_add hhalf hdata, integral_const_mul, integral_const_mul, integral_add hiu hif] at hint
  have hbound : (∫ x in Metric.ball (0 : Plane) R, g x) ≤
      2 * K * ((∫ x in Metric.ball (0 : Plane) R, ‖u x‖ ^ 2) +
        ∫ x in Metric.ball (0 : Plane) R, ‖f x‖ ^ 2) := by linarith only [hint]
  have hlocal (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) r) :
      (∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) = g x := by
    have heq' : ψ =ᶠ[𝓝 x] u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      simp [ψ, hχone y (Metric.ball_subset_closedBall hy)]
    simp only [g, partialDerivative, heq'.fderiv_eq]
  calc
    _ = ∫ x in Metric.ball (0 : Plane) r, g x :=
      setIntegral_congr_fun measurableSet_ball hlocal
    _ ≤ ∫ x in Metric.ball (0 : Plane) R, g x :=
      setIntegral_mono_set hg.integrableOn (ae_of_all _ fun x =>
        Finset.sum_nonneg fun i _ => sq_nonneg _)
        (Filter.Eventually.of_forall (Metric.ball_subset_ball hrR.le))
    _ ≤ _ := hbound

end InfiniteZero
