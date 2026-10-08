import InfiniteZero.LaplacianHessianEnergy
import InfiniteZero.CoordinateDifferentialRules
import InfiniteZero.EllipticCaccioppoli

/-!
# A local second-derivative estimate for the Laplacian

A compactly supported cutoff and the Hessian energy identity give a
local `H²` estimate with a gradient term on the larger ball. The constant
depends only on the two radii. No regularity theorem is used.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace InfiniteZero

theorem coordinateLaplacian_mul {η u : Wavefunction}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) :
    coordinateLaplacian (η * u) = fun x =>
      coordinateLaplacian η x * u x +
        2 * (∑ i : Fin 2, partialDerivative i η x * partialDerivative i u x) +
        η x * coordinateLaplacian u x := by
  have hdη := hη.differentiable (by simp)
  have hdu := hu.differentiable (by simp)
  have hDη (i : Fin 2) := (contDiff_partialDerivative i hη).differentiable (by simp)
  have hDu (i : Fin 2) := (contDiff_partialDerivative i hu).differentiable (by simp)
  have hd (i : Fin 2) :
      partialDerivative i (partialDerivative i (η * u)) =
        partialDerivative i (partialDerivative i η) * u +
          partialDerivative i η * partialDerivative i u +
          (partialDerivative i η * partialDerivative i u +
            η * partialDerivative i (partialDerivative i u)) := by
    rw [partialDerivative_mul i hdη hdu,
      partialDerivative_add i ((hDη i).mul hdu) (hdη.mul (hDu i)),
      partialDerivative_mul i (hDη i) hdu,
      partialDerivative_mul i hdη (hDu i)]
  funext x
  simp only [coordinateLaplacian, Fin.sum_univ_two, hd, Pi.add_apply, Pi.mul_apply]
  ring

theorem tsupport_partialDerivative_subset (u : Wavefunction) (i : Fin 2) :
    tsupport (partialDerivative i u) ⊆ tsupport u :=
  tsupport_fderiv_apply_subset ℝ (coordinateVector i)

theorem coordinateLaplacian_eq_zero_of_notMem_tsupport {u : Wavefunction}
    {x : Plane} (hx : x ∉ tsupport u) : coordinateLaplacian u x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport fun h =>
    hx (tsupport_partialDerivative_subset u i
      (tsupport_partialDerivative_subset (partialDerivative i u) i h))

private theorem norm_laplacian_mul_sq_le {η u : Wavefunction}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) {K : ℝ} (hK : 0 ≤ K)
    (hηK : ∀ x, ‖η x‖ ≤ K)
    (hDK : ∀ i x, ‖partialDerivative i η x‖ ≤ K)
    (hLK : ∀ x, ‖coordinateLaplacian η x‖ ≤ K) (x : Plane) :
    ‖coordinateLaplacian (η * u) x‖ ^ 2 ≤
      16 * K ^ 2 * (‖coordinateLaplacian u x‖ ^ 2 +
        (∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) + ‖u x‖ ^ 2) := by
  have hnorm : ‖coordinateLaplacian (η * u) x‖ ≤
      K * ‖u x‖ + 2 * K * ‖partialDerivative 0 u x‖ +
        2 * K * ‖partialDerivative 1 u x‖ + K * ‖coordinateLaplacian u x‖ := by
    rw [coordinateLaplacian_mul hη hu]
    have hm : ‖partialDerivative 0 η x * partialDerivative 0 u x +
        partialDerivative 1 η x * partialDerivative 1 u x‖ ≤
        K * ‖partialDerivative 0 u x‖ + K * ‖partialDerivative 1 u x‖ := by
      calc
        _ ≤ ‖partialDerivative 0 η x * partialDerivative 0 u x‖ +
            ‖partialDerivative 1 η x * partialDerivative 1 u x‖ := norm_add_le _ _
        _ ≤ _ := by
          simp only [norm_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hDK 0 x) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hDK 1 x) (norm_nonneg _))
    calc
      _ ≤ ‖coordinateLaplacian η x * u x‖ +
          ‖2 * (∑ i : Fin 2, partialDerivative i η x * partialDerivative i u x)‖ +
          ‖η x * coordinateLaplacian u x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ K * ‖u x‖ +
          2 * (K * ‖partialDerivative 0 u x‖ + K * ‖partialDerivative 1 u x‖) +
          K * ‖coordinateLaplacian u x‖ := by
        simp only [norm_mul, Complex.norm_two, Fin.sum_univ_two]
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right (hLK x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hm (by norm_num)))
          (mul_le_mul_of_nonneg_right (hηK x) (norm_nonneg _))
      _ = _ := by ring
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have h1 := sq_nonneg (‖u x‖ - ‖partialDerivative 0 u x‖)
  have h2 := sq_nonneg (‖u x‖ - ‖partialDerivative 1 u x‖)
  have h3 := sq_nonneg (‖u x‖ - ‖coordinateLaplacian u x‖)
  have h4 := sq_nonneg (‖partialDerivative 0 u x‖ - ‖partialDerivative 1 u x‖)
  have h5 := sq_nonneg (‖partialDerivative 0 u x‖ - ‖coordinateLaplacian u x‖)
  have h6 := sq_nonneg (‖partialDerivative 1 u x‖ - ‖coordinateLaplacian u x‖)
  have hsum : (‖u x‖ + 2 * ‖partialDerivative 0 u x‖ +
      2 * ‖partialDerivative 1 u x‖ + ‖coordinateLaplacian u x‖) ^ 2 ≤
      16 * (‖coordinateLaplacian u x‖ ^ 2 +
        (‖partialDerivative 0 u x‖ ^ 2 + ‖partialDerivative 1 u x‖ ^ 2) + ‖u x‖ ^ 2) := by
    nlinarith [sq_nonneg ‖u x‖, sq_nonneg ‖partialDerivative 0 u x‖,
      sq_nonneg ‖partialDerivative 1 u x‖, sq_nonneg ‖coordinateLaplacian u x‖]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg K)
  simp only [Fin.sum_univ_two]
  nlinarith

/-- A fixed cutoff transfers the global Hessian identity to a smaller ball. -/
theorem local_hessian_energy_le_of_cutoff {r R K : ℝ} {η u : Wavefunction}
    (hη : IsTestFunction η) (hu : ContDiff ℝ ∞ u)
    (hs : tsupport η ⊆ Metric.ball (0 : Plane) R)
    (he : Set.EqOn η (fun _ => 1) (Metric.ball (0 : Plane) r))
    (hK : 0 ≤ K) (hηK : ∀ x, ‖η x‖ ≤ K)
    (hDK : ∀ i x, ‖partialDerivative i η x‖ ≤ K)
    (hLK : ∀ x, ‖coordinateLaplacian η x‖ ≤ K) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      ∫ x in Metric.ball (0 : Plane) r, ‖partialDerivative i (partialDerivative j u) x‖ ^ 2) ≤
      16 * K ^ 2 * ((∫ x in Metric.ball (0 : Plane) R, ‖coordinateLaplacian u x‖ ^ 2) +
        (∫ x in Metric.ball (0 : Plane) R, ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) +
        ∫ x in Metric.ball (0 : Plane) R, ‖u x‖ ^ 2) := by
  have hv : IsTestFunction (η * u) := ⟨hη.1.mul hu, hη.2.mul_right⟩
  have hve : Set.EqOn (η * u) u (Metric.ball (0 : Plane) r) := by
    intro x hx
    change η x * u x = u x
    rw [he hx, one_mul]
  have hDD (i j : Fin 2) := partialDerivative_eqOn Metric.isOpen_ball
    (partialDerivative_eqOn Metric.isOpen_ball hve j) i
  have hloc : (∑ i : Fin 2, ∑ j : Fin 2,
      ∫ x in Metric.ball (0 : Plane) r, ‖partialDerivative i (partialDerivative j u) x‖ ^ 2) ≤
        mass (coordinateLaplacian (η * u)) := by
    rw [laplacian_mass_eq_sum_hessian_mass hv]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    calc
      _ = ∫ x in Metric.ball (0 : Plane) r,
          ‖partialDerivative i (partialDerivative j (η * u)) x‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hDD i j hx).symm
      _ ≤ _ := setIntegral_le_integral
        ((hv.partialDerivative j).partialDerivative i).integrable_norm_sq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hz (x : Plane) (hx : x ∉ Metric.ball (0 : Plane) R) :
      ‖coordinateLaplacian (η * u) x‖ ^ 2 = 0 := by
    have hz : coordinateLaplacian (η * u) x = 0 :=
      coordinateLaplacian_eq_zero_of_notMem_tsupport (u := η * u)
        (fun h => hx (hs (tsupport_mul_subset_left h)))
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hL := continuous_integrableOn_norm_sq_ball
    (contDiff_coordinateLaplacian hu).continuous 0 R
  have hU := continuous_integrableOn_norm_sq_ball hu.continuous 0 R
  have hG : IntegrableOn (fun x => ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2)
      (Metric.ball (0 : Plane) R) := integrable_finsetSum Finset.univ fun i _ =>
    continuous_integrableOn_norm_sq_ball (contDiff_partialDerivative i hu).continuous 0 R
  have hLG : IntegrableOn (fun x => ‖coordinateLaplacian u x‖ ^ 2 +
      (∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2)) (Metric.ball (0 : Plane) R) := by
    simpa only [Pi.add_apply] using hL.add hG
  have hLGU : IntegrableOn (fun x => ‖coordinateLaplacian u x‖ ^ 2 +
      (∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) + ‖u x‖ ^ 2)
        (Metric.ball (0 : Plane) R) := by
    simpa only [Pi.add_apply] using hLG.add hU
  calc
    _ ≤ mass (coordinateLaplacian (η * u)) := hloc
    _ = ∫ x in Metric.ball (0 : Plane) R, ‖coordinateLaplacian (η * u) x‖ ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ ≤ ∫ x in Metric.ball (0 : Plane) R,
        16 * K ^ 2 * (‖coordinateLaplacian u x‖ ^ 2 +
          (∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) + ‖u x‖ ^ 2) :=
      setIntegral_mono_on hv.coordinateLaplacian.integrable_norm_sq.integrableOn
        (hLGU.const_mul (16 * K ^ 2)) measurableSet_ball
        (fun x _ => norm_laplacian_mul_sq_le hη.1 hu hK hηK hDK hLK x)
    _ = _ := by
      rw [integral_const_mul, integral_add hLG hU, integral_add hL hG]

/-- Local `H²` control for the Euclidean Laplacian. The constant is chosen
from the radii before the smooth function, so the estimate is uniform. -/
theorem exists_local_poisson_hessian_bound {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C > 0, ∀ u : Wavefunction, ContDiff ℝ ∞ u →
      (∑ i : Fin 2, ∑ j : Fin 2,
        ∫ x in Metric.ball (0 : Plane) r, ‖partialDerivative i (partialDerivative j u) x‖ ^ 2) ≤
        C * ((∫ x in Metric.ball (0 : Plane) R, ‖coordinateLaplacian u x‖ ^ 2) +
          (∫ x in Metric.ball (0 : Plane) R, ∑ i : Fin 2, ‖partialDerivative i u x‖ ^ 2) +
          ∫ x in Metric.ball (0 : Plane) R, ‖u x‖ ^ 2) := by
  obtain ⟨χ, hχ, hc, hb, he, hs, _⟩ := exists_elliptic_cutoff hr hrR
  let η : Wavefunction := fun x => (χ x : ℂ)
  have hη : IsTestFunction η :=
    ⟨Complex.ofRealCLM.contDiff.comp hχ,
      hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)⟩
  obtain ⟨K₀, hk₀⟩ := hη.2.exists_bound_of_continuous hη.1.continuous
  obtain ⟨K₁, hk₁⟩ := (hη.partialDerivative 0).2.exists_bound_of_continuous
    (hη.partialDerivative 0).1.continuous
  obtain ⟨K₂, hk₂⟩ := (hη.partialDerivative 1).2.exists_bound_of_continuous
    (hη.partialDerivative 1).1.continuous
  obtain ⟨K₃, hk₃⟩ := hη.coordinateLaplacian.2.exists_bound_of_continuous
    hη.coordinateLaplacian.1.continuous
  let K := 1 + |K₀| + |K₁| + |K₂| + |K₃|
  have hK : 0 < K := by dsimp [K]; positivity
  have hh₀ : K₀ ≤ K := by
    dsimp [K]
    linarith [le_abs_self K₀, abs_nonneg K₁, abs_nonneg K₂, abs_nonneg K₃]
  have hh₁ : K₁ ≤ K := by
    dsimp [K]
    linarith [le_abs_self K₁, abs_nonneg K₀, abs_nonneg K₂, abs_nonneg K₃]
  have hh₂ : K₂ ≤ K := by
    dsimp [K]
    linarith [le_abs_self K₂, abs_nonneg K₀, abs_nonneg K₁, abs_nonneg K₃]
  have hh₃ : K₃ ≤ K := by
    dsimp [K]
    linarith [le_abs_self K₃, abs_nonneg K₀, abs_nonneg K₁, abs_nonneg K₂]
  refine ⟨16 * K ^ 2, by positivity, fun u hu => ?_⟩
  apply local_hessian_energy_le_of_cutoff hη hu
    ((tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) (by simp) χ).trans hs)
    (fun x hx => by simp only [η, he x (Metric.ball_subset_closedBall hx), Complex.ofReal_one])
    hK.le (fun x => (hk₀ x).trans hh₀) ?_ (fun x => (hk₃ x).trans hh₃)
  intro i x
  fin_cases i
  · exact (hk₁ x).trans hh₁
  · exact (hk₂ x).trans hh₂

end InfiniteZero
