import InfiniteZero.ComplexCuspGeometry
import InfiniteZero.LogFlatActiveWindow

/-!
# Uniform quadratic remainders of the complex cusp radii

The estimates follow from the actual polynomial charts and factorization
of the difference of two squares. No Taylor remainder is an input.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero.Geometry

private theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simp [Complex.sqrt]

private theorem complex_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

/-- A uniform inverse bound for the algebraic factor of the principal root. -/
theorem norm_complexSqrt_sub_linear_le {r : ℝ} (hr : 0 < r) (z ℓ : ℂ)
    (hℓ : ‖ℓ‖ ≤ r / 2) :
    ‖Complex.sqrt z - (r : ℂ) - ℓ‖ ≤
      (2 / r) * ‖z - ((r : ℂ) + ℓ) ^ 2‖ := by
  have hden : r / 2 ≤ ‖Complex.sqrt z + (r : ℂ) + ℓ‖ := by
    have hre := Complex.re_le_norm (Complex.sqrt z + (r : ℂ) + ℓ)
    have hℓre := Complex.abs_re_le_norm ℓ
    have habs := neg_abs_le ℓ.re
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    linarith [complex_sqrt_re_nonneg z]
  have he : (Complex.sqrt z - (r : ℂ) - ℓ) *
      (Complex.sqrt z + (r : ℂ) + ℓ) = z - ((r : ℂ) + ℓ) ^ 2 := by
    calc
      _ = Complex.sqrt z ^ 2 - ((r : ℂ) + ℓ) ^ 2 := by ring
      _ = _ := by rw [complex_sqrt_sq]
  rw [← he, norm_mul]
  apply (mul_le_mul_iff_left₀ hr).mp
  calc
    _ ≤ 2 * (‖Complex.sqrt z - (r : ℂ) - ℓ‖ *
        ‖Complex.sqrt z + (r : ℂ) + ℓ‖) := by
      nlinarith [norm_nonneg (Complex.sqrt z - (r : ℂ) - ℓ)]
    _ = _ := by field_simp

theorem complexSqNorm_cuspPlus_remainder (R s : ℝ) (t : ℂ) :
    complexSqNorm (complexCuspPlus R s t) - ((R : ℂ) + t / 2) ^ 2 =
      ((3 / 4 : ℂ) - ((Real.sqrt 3 * R * s : ℝ) : ℂ)) * t ^ 2 + (s : ℂ) ^ 2 * t ^ 4 := by
  unfold complexSqNorm complexCuspPlus polynomialCuspChart tipPlus normalPlus tangentPlus
  push_cast
  have hs : (Real.sqrt (3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hs]
  ring

theorem complexRadius_cuspMinus_eq_plus (R s : ℝ) (t : ℂ) :
    complexRadius (complexCuspMinus R s t) = complexRadius (complexCuspPlus R s t) := by
  unfold complexRadius
  congr 1
  unfold complexSqNorm complexCuspMinus complexCuspPlus polynomialCuspChart
    tipPlus tipMinus normalPlus normalMinus tangentPlus tangentMinus
  push_cast
  ring

def sourceRadiusRemainderConstant (R s₀ : ℝ) : ℝ :=
  (2 / R) * (3 / 4 + Real.sqrt 3 * R * s₀ + s₀ ^ 2)

theorem norm_complexRadius_cuspPlus_remainder_le {R s₀ s : ℝ}
    (hR : 0 < R) (_hs₀ : 0 ≤ s₀) (hs : |s| ≤ s₀) {t : ℂ}
    (ht1 : ‖t‖ ≤ 1) (htR : ‖t‖ ≤ R) :
    ‖complexRadius (complexCuspPlus R s t) - (R : ℂ) - t / 2‖ ≤
      sourceRadiusRemainderConstant R s₀ * ‖t‖ ^ 2 := by
  have hsabs : ‖(s : ℂ)‖ ≤ s₀ := by simpa using hs
  have hcoef : ‖(3 / 4 : ℂ) - ((Real.sqrt 3 * R * s : ℝ) : ℂ)‖ ≤
      3 / 4 + Real.sqrt 3 * R * s₀ := by
    apply (norm_sub_le _ _).trans
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg 3), abs_of_pos hR]
    norm_num
    gcongr
  have ht4 : ‖t‖ ^ 4 ≤ ‖t‖ ^ 2 := by
    have ht2 : ‖t‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg t]
    nlinarith [sq_nonneg (‖t‖ ^ 2), mul_nonneg (sq_nonneg ‖t‖) (sub_nonneg.2 ht2)]
  have hnum : ‖complexSqNorm (complexCuspPlus R s t) - ((R : ℂ) + t / 2) ^ 2‖ ≤
      (3 / 4 + Real.sqrt 3 * R * s₀ + s₀ ^ 2) * ‖t‖ ^ 2 := by
    rw [complexSqNorm_cuspPlus_remainder]
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_pow]
    have hb1 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖t‖)
    have hb2 := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hsabs 2) ht4
      (by positivity) (sq_nonneg s₀)
    nlinarith
  have hlin : ‖t / (2 : ℂ)‖ ≤ R / 2 := by
    simpa using div_le_div_of_nonneg_right htR (by norm_num : (0 : ℝ) ≤ 2)
  exact (norm_complexSqrt_sub_linear_le hR (complexSqNorm (complexCuspPlus R s t))
    (t / 2) hlin).trans (by
      simpa only [sourceRadiusRemainderConstant, mul_assoc] using
        mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ 2 / R))

theorem norm_complexRadius_cuspMinus_remainder_le {R s₀ r : ℝ}
    (hR : 0 < R) (hs₀ : 0 ≤ s₀) (hr : |r| ≤ s₀) {u : ℂ}
    (hu1 : ‖u‖ ≤ 1) (huR : ‖u‖ ≤ R) :
    ‖complexRadius (complexCuspMinus R r u) - (R : ℂ) - u / 2‖ ≤
      sourceRadiusRemainderConstant R s₀ * ‖u‖ ^ 2 := by
  rw [complexRadius_cuspMinus_eq_plus]
  exact norm_complexRadius_cuspPlus_remainder_le hR hs₀ hr hu1 huR

theorem complexSqNorm_bridge_remainder (R L s r : ℝ) (t u : ℂ) :
    complexSqNorm (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r u)) -
        ((activeDistance R L : ℂ) + (t + u) / 2) ^ 2 =
      2 * ((activeDistance R L : ℂ) + (t + u) / 2) *
        (((Real.sqrt 3 / 2 : ℝ) : ℂ) * ((s : ℂ) * t ^ 2 + (r : ℂ) * u ^ 2)) +
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) * ((s : ℂ) * t ^ 2 + (r : ℂ) * u ^ 2)) ^ 2 +
      (((Real.sqrt 3 / 2 : ℝ) : ℂ) * (t - u) -
        ((s : ℂ) * t ^ 2 - (r : ℂ) * u ^ 2) / 2) ^ 2 := by
  unfold complexSqNorm complexBridge complexCuspPlus complexCuspMinus polynomialCuspChart
    tipPlus tipMinus normalPlus normalMinus tangentPlus tangentMinus activeDistance
  push_cast
  ring

def bridgeRadiusRemainderConstant (D s₀ : ℝ) : ℝ :=
  (2 / D) * (2 * (D + 1) * s₀ + 3 * s₀ ^ 2 + 4)

private theorem bridge_square_remainder_bound {R L s₀ s r : ℝ}
    (hD : 0 < activeDistance R L) (_hs₀ : 0 ≤ s₀) (hs : |s| ≤ s₀) (hr : |r| ≤ s₀)
    {t u : ℂ} (ht : ‖t‖ ≤ 1) (hu : ‖u‖ ≤ 1) :
    ‖complexSqNorm (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r u)) -
        ((activeDistance R L : ℂ) + (t + u) / 2) ^ 2‖ ≤
      (2 * (activeDistance R L + 1) * s₀ + 3 * s₀ ^ 2 + 4) * (‖t‖ ^ 2 + ‖u‖ ^ 2) := by
  let D := activeDistance R L
  let S := ‖t‖ ^ 2 + ‖u‖ ^ 2
  let A := ‖t‖ + ‖u‖
  let γ : ℂ := ((Real.sqrt 3 / 2 : ℝ) : ℂ)
  let v := (s : ℂ) * t ^ 2 + (r : ℂ) * u ^ 2
  let w := (s : ℂ) * t ^ 2 - (r : ℂ) * u ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSle : S ≤ 2 := by dsimp [S]; nlinarith [norm_nonneg t, norm_nonneg u]
  have hSsq : S ^ 2 ≤ 2 * S := by nlinarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAle : A ≤ 2 := by dsimp [A]; linarith
  have hAsq : A ^ 2 ≤ 2 * S := by dsimp [A, S]; nlinarith [sq_nonneg (‖t‖ - ‖u‖)]
  have hγ : ‖γ‖ ≤ 1 := by
    dsimp [γ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg 3]
  have hs' : ‖(s : ℂ)‖ ≤ s₀ := by simpa using hs
  have hr' : ‖(r : ℂ)‖ ≤ s₀ := by simpa using hr
  have hv : ‖v‖ ≤ s₀ * S := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_pow]
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hs' (sq_nonneg ‖t‖),
      mul_le_mul_of_nonneg_right hr' (sq_nonneg ‖u‖)]
  have hw : ‖w‖ ≤ s₀ * S := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, norm_pow]
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hs' (sq_nonneg ‖t‖),
      mul_le_mul_of_nonneg_right hr' (sq_nonneg ‖u‖)]
  have hγv : ‖γ * v‖ ≤ s₀ * S := by
    rw [norm_mul]
    exact (mul_le_mul hγ hv (norm_nonneg v) (by norm_num) |>.trans_eq (one_mul _))
  have hγb : ‖γ * (t - u)‖ ≤ A := by
    rw [norm_mul]
    exact (mul_le_mul hγ (norm_sub_le t u) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hlast : ‖γ * (t - u) - w / 2‖ ≤ A + s₀ * S / 2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_div, Complex.norm_ofNat]
    gcongr
  have hbase : ‖(D : ℂ) + (t + u) / 2‖ ≤ D + 1 := by
    apply (norm_add_le _ _).trans
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, norm_div, Complex.norm_ofNat]
    have := norm_add_le t u
    dsimp [A] at hAle
    linarith
  have hfirst : ‖2 * ((D : ℂ) + (t + u) / 2) * (γ * v)‖ ≤
      2 * (D + 1) * (s₀ * S) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hbase (by norm_num)) hγv
      (norm_nonneg _) (by dsimp [D]; positivity)
  have hsecond : ‖γ * v‖ ^ 2 ≤ 2 * s₀ ^ 2 * S := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hγv 2
    nlinarith [mul_le_mul_of_nonneg_left hSsq (sq_nonneg s₀)]
  have hthird : ‖γ * (t - u) - w / 2‖ ^ 2 ≤ (4 + s₀ ^ 2) * S := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hlast 2
    nlinarith [sq_nonneg (A - s₀ * S / 2),
      mul_le_mul_of_nonneg_left hSsq (sq_nonneg s₀)]
  rw [complexSqNorm_bridge_remainder]
  change ‖2 * ((D : ℂ) + (t + u) / 2) * (γ * v) + (γ * v) ^ 2 +
    (γ * (t - u) - w / 2) ^ 2‖ ≤ _
  apply norm_add₃_le.trans
  simp only [norm_pow]
  change _ ≤ (2 * (D + 1) * s₀ + 3 * s₀ ^ 2 + 4) * S
  nlinarith

theorem norm_complexRadius_bridge_remainder_le {R L s₀ s r : ℝ}
    (hL : R < 2 * L) (hs₀ : 0 ≤ s₀) (hs : |s| ≤ s₀) (hr : |r| ≤ s₀)
    {t u : ℂ} (ht1 : ‖t‖ ≤ 1) (hu1 : ‖u‖ ≤ 1)
    (htD : ‖t‖ ≤ activeDistance R L / 2) (huD : ‖u‖ ≤ activeDistance R L / 2) :
    ‖complexRadius (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r u)) -
        (activeDistance R L : ℂ) - (t + u) / 2‖ ≤
      bridgeRadiusRemainderConstant (activeDistance R L) s₀ * (‖t‖ ^ 2 + ‖u‖ ^ 2) := by
  have hD := activeDistance_pos hL
  have hlin : ‖(t + u) / (2 : ℂ)‖ ≤ activeDistance R L / 2 := by
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le t u
    linarith
  exact (norm_complexSqrt_sub_linear_le hD _ _ hlin).trans (by
    simpa only [bridgeRadiusRemainderConstant, mul_assoc] using
      mul_le_mul_of_nonneg_left (bridge_square_remainder_bound hD hs₀ hs hr ht1 hu1)
        (by positivity : 0 ≤ 2 / activeDistance R L))

theorem sourceRadiusRemainderConstant_pos {R s₀ : ℝ} (hR : 0 < R) (hs₀ : 0 ≤ s₀) :
    0 < sourceRadiusRemainderConstant R s₀ := by
  unfold sourceRadiusRemainderConstant
  positivity

theorem bridgeRadiusRemainderConstant_pos {D s₀ : ℝ} (hD : 0 < D) (hs₀ : 0 ≤ s₀) :
    0 < bridgeRadiusRemainderConstant D s₀ := by
  unfold bridgeRadiusRemainderConstant
  positivity

/-- One fixed holomorphic bidisc and one positive constant control all three
true radii uniformly in both bounded real tangential variables. -/
theorem exists_uniform_complexCusp_radius_remainders {R L s₀ : ℝ}
    (hR : 0 < R) (hL : R < 2 * L) (hs₀ : 0 ≤ s₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (s r : ℝ), |s| ≤ s₀ → |r| ≤ s₀ →
      ∀ (t u : ℂ), ‖t‖ < δ → ‖u‖ < δ →
        (t, u) ∈ complexCuspRadiusDomain R L s r ∧
        ‖complexRadius (complexCuspPlus R s t) - (R : ℂ) - t / 2‖ ≤ C * ‖t‖ ^ 2 ∧
        ‖complexRadius (complexCuspMinus R r u) - (R : ℂ) - u / 2‖ ≤ C * ‖u‖ ^ 2 ∧
        ‖complexRadius (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r u)) -
          (activeDistance R L : ℂ) - (t + u) / 2‖ ≤ C * (‖t‖ ^ 2 + ‖u‖ ^ 2) := by
  obtain ⟨ε, hε, he⟩ := exists_uniform_complexCusp_bidisc hR hL s₀
  let δ := min ε (min 1 (min R (activeDistance R L / 2)))
  let C := sourceRadiusRemainderConstant R s₀ + bridgeRadiusRemainderConstant (activeDistance R L) s₀
  have hD := activeDistance_pos hL
  have hcs := sourceRadiusRemainderConstant_pos hR hs₀
  have hcb := bridgeRadiusRemainderConstant_pos hD hs₀
  have hδ : 0 < δ := lt_min hε (lt_min (by norm_num) (lt_min hR (half_pos hD)))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ R := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδD : δ ≤ activeDistance R L / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, C, hδ, add_pos hcs hcb, fun s r hs hr t u ht hu => ?_⟩
  refine ⟨he s r hs hr t u (ht.trans_le hδε) (hu.trans_le hδε), ?_, ?_, ?_⟩
  · exact (norm_complexRadius_cuspPlus_remainder_le hR hs₀ hs
      (ht.le.trans hδ1) (ht.le.trans hδR)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _))
  · exact (norm_complexRadius_cuspMinus_remainder_le hR hs₀ hr
      (hu.le.trans hδ1) (hu.le.trans hδR)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _))
  · exact (norm_complexRadius_bridge_remainder_le hL hs₀ hs hr
      (ht.le.trans hδ1) (hu.le.trans hδ1) (ht.le.trans hδD) (hu.le.trans hδD)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity))

/-- All three geometric remainders divided by `h` vanish uniformly on the
actual `h^(3/4)` complex window. -/
theorem eventually_complexCusp_radius_remainders_div_small {R L s₀ tStar : ℝ}
    (hR : 0 < R) (hL : R < 2 * L) (hs₀ : 0 ≤ s₀) (_htStar : 0 < tStar)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ (s r : ℝ), |s| ≤ s₀ → |r| ≤ s₀ →
      ∀ (t u : ℂ), ‖t‖ ≤ logFlatActiveWindow tStar h → ‖u‖ ≤ logFlatActiveWindow tStar h →
        (‖complexRadius (complexCuspPlus R s t) - (R : ℂ) - t / 2‖ +
          ‖complexRadius (complexCuspMinus R r u) - (R : ℂ) - u / 2‖ +
          ‖complexRadius (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r u)) -
            (activeDistance R L : ℂ) - (t + u) / 2‖) / h ≤ η := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := exists_uniform_complexCusp_radius_remainders hR hL hs₀
  have hlim : Tendsto (fun h : ℝ => 4 * C * (logFlatActiveWindow tStar h ^ 2 / h))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_logFlatActiveWindow_sq_div tStar).const_mul (4 * C)
  filter_upwards [(tendsto_logFlatActiveWindow tStar).eventually (gt_mem_nhds hδ),
    hlim.eventually (gt_mem_nhds hη), self_mem_nhdsWithin] with h hwindow hsmall hh
  intro s r hs hr t u ht hu
  have hhp : 0 < h := hh
  obtain ⟨_, hp, hm, hbr⟩ := hb s r hs hr t u (ht.trans_lt hwindow) (hu.trans_lt hwindow)
  have htsq := pow_le_pow_left₀ (norm_nonneg t) ht 2
  have husq := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hnorm :
      ‖complexRadius (complexCuspPlus R s t) - (R : ℂ) - t / 2‖ +
        ‖complexRadius (complexCuspMinus R r u) - (R : ℂ) - u / 2‖ +
        ‖complexRadius (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r u)) -
          (activeDistance R L : ℂ) - (t + u) / 2‖ ≤
      4 * C * logFlatActiveWindow tStar h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left htsq hC.le, mul_le_mul_of_nonneg_left husq hC.le]
  calc
    _ ≤ (4 * C * logFlatActiveWindow tStar h ^ 2) / h :=
      div_le_div_of_nonneg_right hnorm hhp.le
    _ = 4 * C * (logFlatActiveWindow tStar h ^ 2 / h) := by ring
    _ ≤ η := hsmall.le

end InfiniteZero.Geometry
