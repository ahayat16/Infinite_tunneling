import InfiniteZero.LocalPoissonH2
import InfiniteZero.CoordinateSobolevCalculus
import InfiniteZero.EllipticUniformContract

/-!
# Uniform local gain of two derivatives at order zero

The cutoff energy estimate controls the gradient on an intermediate ball.
The equation then controls the Laplacian there, and the compact-support
Hessian identity controls all second derivatives on the inner ball.
The resulting constant is uniform over bounded complex lower-order
coefficients.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace InfiniteZero

theorem coordinateSobolevNorm_two_sq {u : Wavefunction} (hu : ContDiff ℝ ∞ u)
    (r : ℝ) : coordinateSobolevNorm 2 r u ^ 2 =
      (∫ x in Metric.ball (0 : Plane) r, ‖u x‖ ^ 2) +
      (∫ x in Metric.ball (0 : Plane) r, ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) +
      ∑ i : Fin 2, ∑ j : Fin 2,
        ∫ x in Metric.ball (0 : Plane) r, ‖partialDerivative i (partialDerivative j u) x‖ ^ 2 := by
  rw [coordinateSobolevNorm_succ_sq hu 1, coordinateSobolevNorm_zero,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    continuous_integrableOn_norm_sq_ball (contDiff_partialDerivative i hu).continuous 0 r)]
  simp_rw [coordinateSobolevNorm_one_sq (contDiff_partialDerivative _ hu), Fin.sum_univ_two]
  ring

/-- Bounded lower-order coefficients convert the equation into a pointwise
bound for the Laplacian. No reality or sign assumption is needed. -/
theorem laplacian_sq_le_of_elliptic_equation {a : Fin 2 → Wavefunction}
    {q u f : Wavefunction} {B : ℝ} (hB : 0 ≤ B) {x : Plane}
    (hcoeff : (∀ i, ‖a i x‖ ≤ B) ∧ ‖q x‖ ≤ B)
    (heq : ellipticExpression a q u x = f x) :
    ‖coordinateLaplacian u x‖ ^ 2 ≤
      4 * (‖f x‖ ^ 2 + B ^ 2 *
        ((∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) + ‖u x‖ ^ 2)) := by
  have hl : coordinateLaplacian u x =
      (∑ i : Fin 2, a i x * partialDerivative i u x) + q x * u x - f x := by
    change -coordinateLaplacian u x +
      (∑ i : Fin 2, a i x * partialDerivative i u x) + q x * u x = f x at heq
    linear_combination -heq
  have hn : ‖coordinateLaplacian u x‖ ≤
      B * ‖partialDerivative 0 u x‖ + B * ‖partialDerivative 1 u x‖ +
        B * ‖u x‖ + ‖f x‖ := by
    rw [hl, Fin.sum_univ_two]
    calc
      _ ≤ ‖a 0 x * partialDerivative 0 u x + a 1 x * partialDerivative 1 u x + q x * u x‖ +
          ‖f x‖ := norm_sub_le _ _
      _ ≤ (‖a 0 x * partialDerivative 0 u x‖ + ‖a 1 x * partialDerivative 1 u x‖ +
          ‖q x * u x‖) + ‖f x‖ :=
        add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
      _ ≤ _ := by
        simp only [norm_mul]
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right (hcoeff.1 0) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hcoeff.1 1) (norm_nonneg _)))
          (mul_le_mul_of_nonneg_right hcoeff.2 (norm_nonneg _))) le_rfl
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (B * ‖partialDerivative 0 u x‖ - B * ‖partialDerivative 1 u x‖),
    sq_nonneg (B * ‖partialDerivative 0 u x‖ - B * ‖u x‖),
    sq_nonneg (B * ‖partialDerivative 0 u x‖ - ‖f x‖),
    sq_nonneg (B * ‖partialDerivative 1 u x‖ - B * ‖u x‖),
    sq_nonneg (B * ‖partialDerivative 1 u x‖ - ‖f x‖),
    sq_nonneg (B * ‖u x‖ - ‖f x‖)]

/-- The order-zero uniform interior elliptic estimate is proved from
integration by parts and smooth cutoffs. -/
theorem hasLocalCoordinateEllipticEstimate_zero : HasLocalCoordinateEllipticEstimate 0 := by
  intro r R hr hrR B hB
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hs : 0 < s := hr.trans hrs
  obtain ⟨Cg, hCg, hgrad⟩ := exists_elliptic_local_gradient_bound hs hsR hB
  obtain ⟨Cp, hCp, hpoisson⟩ := exists_local_poisson_hessian_bound hr hrs
  let D := 4 * (1 + B ^ 2 * (Cg + 1))
  let M := 1 + Cg + Cp * (D + Cg + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨Real.sqrt M, Real.sqrt_pos.mpr hM, ?_⟩
  intro a q u f _ha _hq hu hf hcoeff heq
  let U (t : ℝ) := ∫ x in Metric.ball (0 : Plane) t, ‖u x‖ ^ 2
  let F (t : ℝ) := ∫ x in Metric.ball (0 : Plane) t, ‖f x‖ ^ 2
  let G (t : ℝ) := ∫ x in Metric.ball (0 : Plane) t, ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2
  let L := ∫ x in Metric.ball (0 : Plane) s, ‖coordinateLaplacian u x‖ ^ 2
  let W := U R + F R
  have hUn (t : ℝ) : 0 ≤ U t := integral_nonneg fun _ => sq_nonneg _
  have hFn (t : ℝ) : 0 ≤ F t := integral_nonneg fun _ => sq_nonneg _
  have hGn (t : ℝ) : 0 ≤ G t := integral_nonneg fun _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0 ≤ W := add_nonneg (hUn R) (hFn R)
  have hiU (t : ℝ) := continuous_integrableOn_norm_sq_ball hu.continuous 0 t
  have hiF (t : ℝ) := continuous_integrableOn_norm_sq_ball hf.continuous 0 t
  have hiG (t : ℝ) : IntegrableOn
      (fun x => ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) (Metric.ball (0 : Plane) t) :=
    integrable_finsetSum Finset.univ fun i _ =>
      continuous_integrableOn_norm_sq_ball (contDiff_partialDerivative i hu).continuous 0 t
  have hUr : U r ≤ U R := setIntegral_mono_set (hiU R)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ hx => Metric.ball_subset_ball hrR.le hx)
  have hUs : U s ≤ U R := setIntegral_mono_set (hiU R)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ hx => Metric.ball_subset_ball hsR.le hx)
  have hFs : F s ≤ F R := setIntegral_mono_set (hiF R)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ hx => Metric.ball_subset_ball hsR.le hx)
  have hGrs : G r ≤ G s := setIntegral_mono_set (hiG s)
    (Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ hx => Metric.ball_subset_ball hrs.le hx)
  have hGs : G s ≤ Cg * W := hgrad a q u f hu hf
    (fun _ hx => hcoeff.values hx) heq
  have hL : L ≤ 4 * (F s + B ^ 2 * (G s + U s)) := by
    have hGU : IntegrableOn (fun x => (∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) +
        ‖u x‖ ^ 2) (Metric.ball (0 : Plane) s) := by
      simpa only [Pi.add_apply] using (hiG s).add (hiU s)
    have hFB : IntegrableOn (fun x => ‖f x‖ ^ 2 + B ^ 2 *
        ((∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) + ‖u x‖ ^ 2))
          (Metric.ball (0 : Plane) s) := by
      simpa only [Pi.add_apply] using (hiF s).add (hGU.const_mul (B ^ 2))
    calc
      _ ≤ ∫ x in Metric.ball (0 : Plane) s,
          4 * (‖f x‖ ^ 2 + B ^ 2 *
            ((∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) + ‖u x‖ ^ 2)) :=
        setIntegral_mono_on
          (continuous_integrableOn_norm_sq_ball (contDiff_coordinateLaplacian hu).continuous 0 s)
          (hFB.const_mul 4) measurableSet_ball (fun x hx =>
            laplacian_sq_le_of_elliptic_equation hB
              (hcoeff.values (Metric.ball_subset_ball hsR.le hx))
              (heq x (Metric.ball_subset_ball hsR.le hx)))
      _ = _ := by
        rw [integral_const_mul, integral_add (hiF s) (hGU.const_mul (B ^ 2)),
          integral_const_mul, integral_add (hiG s) (hiU s)]
  have hUW : U R ≤ W := le_add_of_nonneg_right (hFn R)
  have hFW : F R ≤ W := le_add_of_nonneg_left (hUn R)
  have hLW : L ≤ D * W := by
    calc
      L ≤ 4 * (F s + B ^ 2 * (G s + U s)) := hL
      _ ≤ 4 * (W + B ^ 2 * (Cg * W + W)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (hFs.trans hFW)
          (mul_le_mul_of_nonneg_left (add_le_add hGs (hUs.trans hUW)) (sq_nonneg B)))
          (by norm_num)
      _ = D * W := by dsimp [D]; ring
  have hH := hpoisson u hu
  change (∑ i : Fin 2, ∑ j : Fin 2,
      ∫ x in Metric.ball (0 : Plane) r, ‖partialDerivative i (partialDerivative j u) x‖ ^ 2) ≤
        Cp * (L + G s + U s) at hH
  have hH' : (∑ i : Fin 2, ∑ j : Fin 2,
      ∫ x in Metric.ball (0 : Plane) r, ‖partialDerivative i (partialDerivative j u) x‖ ^ 2) ≤
        Cp * (D + Cg + 1) * W := by
    calc
      _ ≤ Cp * (L + G s + U s) := hH
      _ ≤ Cp * (D * W + Cg * W + W) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hLW hGs) (hUs.trans hUW)) hCp.le
      _ = _ := by ring
  have hsq : coordinateSobolevNorm 2 r u ^ 2 ≤ M * W := by
    rw [coordinateSobolevNorm_two_sq hu]
    change U r + G r + _ ≤ M * W
    have hUrW := hUr.trans hUW
    have hGrW := hGrs.trans hGs
    dsimp [M]
    nlinarith
  have hWR : W ≤ (coordinateSobolevNorm 0 R u + coordinateSobolevNorm 0 R f) ^ 2 := by
    have hU : coordinateSobolevNorm 0 R u ^ 2 = U R := by
      rw [coordinateSobolevNorm_zero, Real.sq_sqrt (hUn R)]
    have hF : coordinateSobolevNorm 0 R f ^ 2 = F R := by
      rw [coordinateSobolevNorm_zero, Real.sq_sqrt (hFn R)]
    have hp := mul_nonneg (coordinateSobolevNorm_nonneg 0 R u)
      (coordinateSobolevNorm_nonneg 0 R f)
    dsimp [W]
    nlinarith
  have hfin := hsq.trans (mul_le_mul_of_nonneg_left hWR hM.le)
  have hroot : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM.le
  have hn : 0 ≤ Real.sqrt M * (coordinateSobolevNorm 0 R u + coordinateSobolevNorm 0 R f) :=
    mul_nonneg (Real.sqrt_nonneg M) (add_nonneg (coordinateSobolevNorm_nonneg 0 R u)
      (coordinateSobolevNorm_nonneg 0 R f))
  apply (sq_le_sq₀ (coordinateSobolevNorm_nonneg 2 r u) hn).mp
  simpa only [mul_pow, hroot] using hfin

end InfiniteZero
