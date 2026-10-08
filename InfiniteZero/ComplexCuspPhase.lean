import InfiniteZero.ComplexCuspRemainder

/-!
# Magnetic phase on the actual complex cusp charts

The polynomial extension agrees with the real magnetic phase. Its exact
expansion has constant term `phaseStar`, linear term `phaseSlope * (t + u)`,
and a uniformly quadratic remainder on bounded tangential charts. The
exponential of that remainder divided by `h` tends to one on the active window.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero.Geometry

/-- Polynomial complexification of the real magnetic phase, with the same sign. -/
def complexPhase (b L : ℝ) (z w : ComplexPoint) : ℂ :=
  (b : ℂ) * ((L : ℂ) * (z.2 - w.2) + (z.1 * w.2 - z.2 * w.1) / 2)

@[simp] theorem complexPhase_complexifyPoint (b L : ℝ) (z w : Point) :
    complexPhase b L (complexifyPoint z) (complexifyPoint w) = (phase b L z w : ℂ) := by
  simp [complexPhase, complexifyPoint, phase, wedge]

@[simp] theorem complexPhase_at_tips (b R L : ℝ) :
    complexPhase b L (complexifyPoint (tipPlus R)) (complexifyPoint (tipMinus R)) =
      (phaseStar b R L : ℂ) := by
  rw [complexPhase_complexifyPoint, phase_at_tips]

@[simp] theorem complexPhase_cusps_zero (b R L s r : ℝ) :
    complexPhase b L (complexCuspPlus R s 0) (complexCuspMinus R r 0) =
      (phaseStar b R L : ℂ) := by
  simp only [complexCuspPlus, complexCuspMinus, polynomialCuspChart_zero,
    complexPhase_at_tips]

def complexCuspPhaseRemainder (b R L s r : ℝ) (t u : ℂ) : ℂ :=
  complexPhase b L (complexCuspPlus R s t) (complexCuspMinus R r u) -
    (phaseStar b R L : ℂ) - (phaseSlope b L : ℂ) * (t + u)

/-- The full polynomial remainder; in particular, all of its normal monomials
have degree at least two. -/
theorem complexCuspPhaseRemainder_eq (b R L s r : ℝ) (t u : ℂ) :
    complexCuspPhaseRemainder b R L s r t u = (b : ℂ) / 4 *
      (2 * ((R - L : ℝ) : ℂ) * ((s : ℂ) * t ^ 2 + (r : ℂ) * u ^ 2) +
        (Real.sqrt 3 : ℂ) * t * u +
        ((s : ℂ) * t ^ 2 * u + (r : ℂ) * t * u ^ 2) -
        (Real.sqrt 3 : ℂ) * (s : ℂ) * (r : ℂ) * t ^ 2 * u ^ 2) := by
  unfold complexCuspPhaseRemainder complexPhase complexCuspPlus complexCuspMinus
    polynomialCuspChart tipPlus tipMinus normalPlus normalMinus tangentPlus tangentMinus
    phaseStar phaseSlope
  push_cast
  have hs : (Real.sqrt (3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hs]
  ring

/-- A completely explicit uniform bound for the phase remainder. -/
def cuspPhaseRemainderConstant (b R L s₀ : ℝ) : ℝ :=
  |b| / 4 * (2 * |R - L| * s₀ + Real.sqrt 3 + s₀ + Real.sqrt 3 * s₀ ^ 2)

theorem cuspPhaseRemainderConstant_nonneg (b R L : ℝ) {s₀ : ℝ} (hs₀ : 0 ≤ s₀) :
    0 ≤ cuspPhaseRemainderConstant b R L s₀ := by
  unfold cuspPhaseRemainderConstant
  positivity

theorem norm_complexCuspPhaseRemainder_le {b R L s₀ s r : ℝ}
    (hs₀ : 0 ≤ s₀) (hs : |s| ≤ s₀) (hr : |r| ≤ s₀)
    {t u : ℂ} (ht : ‖t‖ ≤ 1) (hu : ‖u‖ ≤ 1) :
    ‖complexCuspPhaseRemainder b R L s r t u‖ ≤
      cuspPhaseRemainderConstant b R L s₀ * (‖t‖ ^ 2 + ‖u‖ ^ 2) := by
  let S := ‖t‖ ^ 2 + ‖u‖ ^ 2
  let q := Real.sqrt (3 : ℝ)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hs' : ‖(s : ℂ)‖ ≤ s₀ := by simpa using hs
  have hr' : ‖(r : ℂ)‖ ≤ s₀ := by simpa using hr
  have hprod : ‖t‖ * ‖u‖ ≤ S := by
    dsimp [S]
    nlinarith only [sq_nonneg (‖t‖ - ‖u‖), sq_nonneg ‖t‖, sq_nonneg ‖u‖]
  have hprod2 : ‖t‖ ^ 2 * ‖u‖ ^ 2 ≤ S := by
    have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    dsimp [S]
    nlinarith only [mul_le_mul_of_nonneg_left hu2 (sq_nonneg ‖t‖), sq_nonneg ‖u‖]
  have hfirst : ‖2 * ((R - L : ℝ) : ℂ) *
      ((s : ℂ) * t ^ 2 + (r : ℂ) * u ^ 2)‖ ≤ 2 * |R - L| * s₀ * S := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    have hb : ‖(s : ℂ) * t ^ 2 + (r : ℂ) * u ^ 2‖ ≤ s₀ * S := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul, norm_pow]
      dsimp [S]
      nlinarith only [mul_le_mul_of_nonneg_right hs' (sq_nonneg ‖t‖),
        mul_le_mul_of_nonneg_right hr' (sq_nonneg ‖u‖)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * |R - L|)
  have hsecond : ‖(q : ℂ) * t * u‖ ≤ q * S := by
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq]
    nlinarith only [mul_le_mul_of_nonneg_left hprod hq]
  have hthird : ‖(s : ℂ) * t ^ 2 * u + (r : ℂ) * t * u ^ 2‖ ≤ s₀ * S := by
    have hp : ‖(s : ℂ)‖ * ‖u‖ ≤ s₀ :=
      (mul_le_mul hs' hu (norm_nonneg u) hs₀).trans_eq (mul_one s₀)
    have hm : ‖(r : ℂ)‖ * ‖t‖ ≤ s₀ :=
      (mul_le_mul hr' ht (norm_nonneg t) hs₀).trans_eq (mul_one s₀)
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_pow]
    dsimp [S]
    nlinarith only [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖t‖),
      mul_le_mul_of_nonneg_right hm (sq_nonneg ‖u‖)]
  have hfourth : ‖(q : ℂ) * (s : ℂ) * (r : ℂ) * t ^ 2 * u ^ 2‖ ≤
      q * s₀ ^ 2 * S := by
    have hsr : ‖(s : ℂ)‖ * ‖(r : ℂ)‖ ≤ s₀ ^ 2 := by
      simpa only [pow_two] using mul_le_mul hs' hr' (norm_nonneg _) hs₀
    have hsrq := mul_le_mul_of_nonneg_left hsr hq
    have hb := mul_le_mul hsrq hprod2 (by positivity) (mul_nonneg hq (sq_nonneg s₀))
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hq,
      mul_assoc] using hb
  have hsum : ‖2 * ((R - L : ℝ) : ℂ) *
      ((s : ℂ) * t ^ 2 + (r : ℂ) * u ^ 2) + (q : ℂ) * t * u +
      ((s : ℂ) * t ^ 2 * u + (r : ℂ) * t * u ^ 2) -
      (q : ℂ) * (s : ℂ) * (r : ℂ) * t ^ 2 * u ^ 2‖ ≤
      (2 * |R - L| * s₀ + q + s₀ + q * s₀ ^ 2) * S := by
    apply (norm_sub_le _ _).trans
    apply (add_le_add norm_add₃_le le_rfl).trans
    nlinarith only [hfirst, hsecond, hthird, hfourth]
  rw [complexCuspPhaseRemainder_eq, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ |b| / 4)).trans_eq (by
    dsimp [cuspPhaseRemainderConstant, S, q]
    ring)

/-- The true phase error divided by `h` vanishes for arbitrary bounded moving
tangential parameters and complex normals in the active window. -/
theorem tendsto_complexCuspPhaseRemainder_div
    {ι : Type*} {l : Filter ι} {h s r : ι → ℝ} {t u : ι → ℂ}
    {b R L s₀ tStar M : ℝ} (hs₀ : 0 ≤ s₀)
    (hh : Tendsto h l (𝓝[>] 0))
    (hs : ∀ᶠ i in l, |s i| ≤ s₀) (hr : ∀ᶠ i in l, |r i| ≤ s₀)
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ M * logFlatActiveWindow tStar (h i))
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => complexCuspPhaseRemainder b R L (s i) (r i) (t i) (u i) /
      (h i : ℂ)) l (𝓝 0) := by
  let C := cuspPhaseRemainderConstant b R L s₀
  have hC : 0 ≤ C := cuspPhaseRemainderConstant_nonneg b R L hs₀
  have hW : Tendsto (fun i => M * logFlatActiveWindow tStar (h i)) l (𝓝 0) := by
    simpa using ((tendsto_logFlatActiveWindow tStar).comp hh).const_mul M
  apply squeeze_zero_norm' (a := fun i => (2 * C * M ^ 2) *
    (logFlatActiveWindow tStar (h i) ^ 2 / h i)) ?_ ?_
  · filter_upwards [hs, hr, ht, hu, hh.eventually self_mem_nhdsWithin,
      hW.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with i hsi hri hti hui hhi hw
    have hp : 0 < h i := hhi
    have hb := norm_complexCuspPhaseRemainder_le (b := b) (R := R) (L := L)
      hs₀ hsi hri (hti.trans hw) (hui.trans hw)
    have htsq := pow_le_pow_left₀ (norm_nonneg (t i)) hti 2
    have husq := pow_le_pow_left₀ (norm_nonneg (u i)) hui 2
    rw [mul_pow] at htsq husq
    have hn : ‖complexCuspPhaseRemainder b R L (s i) (r i) (t i) (u i)‖ ≤
        (2 * C * M ^ 2) * logFlatActiveWindow tStar (h i) ^ 2 := by
      change _ ≤ C * (‖t i‖ ^ 2 + ‖u i‖ ^ 2) at hb
      nlinarith only [hb, mul_le_mul_of_nonneg_left htsq hC, mul_le_mul_of_nonneg_left husq hC]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hn hp.le
  · simpa using ((tendsto_logFlatActiveWindow_sq_div tStar).comp hh).const_mul (2 * C * M ^ 2)

/-- The correction to the constant and linear magnetic phase tends to one. -/
theorem tendsto_complexCuspPhase_correction
    {ι : Type*} {l : Filter ι} {h s r : ι → ℝ} {t u : ι → ℂ}
    {b R L s₀ tStar M : ℝ} (hs₀ : 0 ≤ s₀)
    (hh : Tendsto h l (𝓝[>] 0))
    (hs : ∀ᶠ i in l, |s i| ≤ s₀) (hr : ∀ᶠ i in l, |r i| ≤ s₀)
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ M * logFlatActiveWindow tStar (h i))
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => Complex.exp (Complex.I *
      (complexPhase b L (complexCuspPlus R (s i) (t i)) (complexCuspMinus R (r i) (u i)) -
        (phaseStar b R L : ℂ) - (phaseSlope b L : ℂ) * (t i + u i)) / (h i : ℂ)))
      l (𝓝 1) := by
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_complexCuspPhaseRemainder_div (b := b) (R := R) (L := L) hs₀ hh hs hr ht hu).const_mul
      Complex.I)
  simpa only [complexCuspPhaseRemainder, mul_div_assoc, mul_zero, Complex.exp_zero] using he

end InfiniteZero.Geometry
