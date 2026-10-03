import InfiniteZero.ComplexLandauKernel
import InfiniteZero.LandauLaplaceUniformLeading
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The local Landau profile with a small complex radial perturbation

The normalization retains the moving real energy and radius. Its linear
radial term cancels exactly, leaving a perturbation that vanishes when
`δ / sqrt h → 0`. The real proper-time contour is unchanged.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def properTimeRadialCoefficient (b τ : ℝ) : ℝ :=
  b / 4 * (Real.cosh (b * τ) / Real.sinh (b * τ))

def complexLandauPhaseRemainder (b E r : ℝ) (δ : ℂ) (τ : ℝ) : ℂ :=
  2 * (r : ℂ) * δ * ((properTimeRadialCoefficient b τ -
    properTimeRadialCoefficient b (bridgeTime b E r) : ℝ) : ℂ) +
      δ ^ 2 * (properTimeRadialCoefficient b τ : ℂ)

def complexLandauLocalProfile (b E r ε h : ℝ) (δ : ℂ) (u : ℝ) : ℂ :=
  (landauLocalProfile b E r ε h u : ℂ) *
    Complex.exp (-complexLandauPhaseRemainder b E r δ
      (bridgeTime b E r + Real.sqrt h * u) / (h : ℂ))

theorem contDiffAt_properTimeRadialCoefficient {b τ : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) (n : ℕ∞) :
    ContDiffAt ℝ n (properTimeRadialCoefficient b) τ := by
  have hs : Real.sinh (b * τ) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hb hτ)).ne'
  unfold properTimeRadialCoefficient
  fun_prop

theorem deriv_bridgeAction_eq_radialCoefficient {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    deriv (bridgeAction b E) r =
      2 * r * properTimeRadialCoefficient b (bridgeTime b E r) := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
  have hs2 := Real.sq_sqrt hE.le
  have hA : 0 < b ^ 2 * r ^ 2 + 4 * E := by positivity
  have hA2 := Real.sq_sqrt hA.le
  have hroot : Real.sqrt (1 + (b * r / (2 * Real.sqrt E)) ^ 2) =
      Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) / (2 * Real.sqrt E) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    field_simp
    nlinarith
  rw [deriv_bridgeAction hb.ne' hE]
  simp only [properTimeRadialCoefficient, bridgeTime, mul_div_cancel₀ _ hb.ne',
    Real.cosh_arsinh, Real.sinh_arsinh, hroot]
  field_simp
  ring

/-- Exact cancellation of the linear radial action term. -/
theorem complexLandauPhase_sub_linear {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (δ : ℂ) (τ : ℝ) :
    (E * τ : ℝ) + (properTimeRadialCoefficient b τ : ℂ) * ((r : ℂ) + δ) ^ 2 -
        ((bridgeAction b E r : ℂ) + ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) =
      ((properTimePhase b E r τ - bridgeAction b E r : ℝ) : ℂ) +
        complexLandauPhaseRemainder b E r δ τ := by
  rw [deriv_bridgeAction_eq_radialCoefficient hb hE hr]
  unfold complexLandauPhaseRemainder properTimePhase properTimeRadialCoefficient
  push_cast
  ring

/-- The profile is exactly the rescaled original integrand with normalization
`exp ((J + J' δ) / h)` on the local interval. -/
theorem complexLandauLocalProfile_eq_normalized {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (ε h : ℝ) (δ : ℂ) (u : ℝ) :
    complexLandauLocalProfile b E r ε h δ u =
      (Ioo (bridgeTime b E r - ε) (bridgeTime b E r + ε)).indicator
        (fun τ => Complex.exp (((bridgeAction b E r : ℂ) +
          ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
            complexLandauIntegrand b h E ((r : ℂ) + δ) τ)
        (bridgeTime b E r + Real.sqrt h * u) := by
  let τ := bridgeTime b E r + Real.sqrt h * u
  by_cases hmem : τ ∈ Ioo (bridgeTime b E r - ε) (bridgeTime b E r + ε)
  · dsimp only [τ] at hmem
    simp only [complexLandauLocalProfile, landauLocalProfile, indicator_of_mem hmem]
    unfold complexLandauIntegrand
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    have he := complexLandauPhase_sub_linear hb hE hr δ τ
    unfold properTimeRadialCoefficient at he
    dsimp only [τ] at he
    push_cast at he
    linear_combination (h : ℂ)⁻¹ * he
  · dsimp only [τ] at hmem
    simp only [complexLandauLocalProfile, landauLocalProfile, indicator_of_notMem hmem,
      Complex.ofReal_zero, zero_mul]

theorem measurable_complexLandauLocalProfile (b E r ε h : ℝ) (δ : ℂ) :
    Measurable (complexLandauLocalProfile b E r ε h δ) := by
  unfold complexLandauLocalProfile complexLandauPhaseRemainder properTimeRadialCoefficient
  have hm := measurable_landauLocalProfile b E r ε h
  fun_prop

theorem complexLandauPhaseRemainder_div_eq (b E r : ℝ) {h : ℝ} (hh : 0 < h)
    (δ : ℂ) (u : ℝ) :
    complexLandauPhaseRemainder b E r δ (bridgeTime b E r + Real.sqrt h * u) / (h : ℂ) =
      2 * (r : ℂ) * (δ / (Real.sqrt h : ℂ)) *
        (((properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) -
          properTimeRadialCoefficient b (bridgeTime b E r)) / Real.sqrt h : ℝ) : ℂ) +
      (δ / (Real.sqrt h : ℂ)) ^ 2 *
        (properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) : ℂ) := by
  have hs : (Real.sqrt h : ℂ) ^ 2 = (h : ℂ) := by exact_mod_cast Real.sq_sqrt hh.le
  unfold complexLandauPhaseRemainder
  push_cast
  rw [← hs]
  ring

theorem norm_complexLandauPhaseRemainder_div_le {b E r h L Q : ℝ}
    (hh : 0 < h) (hr : 0 ≤ r) (δ : ℂ) (u : ℝ)
    (hδ : ‖δ / (Real.sqrt h : ℂ)‖ ≤ 1)
    (hLip : |properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) -
        properTimeRadialCoefficient b (bridgeTime b E r)| ≤ L * |Real.sqrt h * u|)
    (hq : |properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u)| ≤ Q) :
    ‖complexLandauPhaseRemainder b E r δ (bridgeTime b E r + Real.sqrt h * u) / (h : ℂ)‖ ≤
      2 * r * L * |u| + Q := by
  rw [complexLandauPhaseRemainder_div_eq b E r hh δ u]
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hquot : ‖(((properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) -
      properTimeRadialCoefficient b (bridgeTime b E r)) / Real.sqrt h : ℝ) : ℂ)‖ ≤ L * |u| := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    rw [abs_mul, abs_of_pos hs] at hLip
    nlinarith only [hLip]
  calc
    _ ≤ ‖2 * (r : ℂ) * (δ / (Real.sqrt h : ℂ))‖ *
        ‖(((properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) -
          properTimeRadialCoefficient b (bridgeTime b E r)) / Real.sqrt h : ℝ) : ℂ)‖ +
        ‖δ / (Real.sqrt h : ℂ)‖ ^ 2 *
          ‖(properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) : ℂ)‖ := by
      convert norm_add_le
        (2 * (r : ℂ) * (δ / (Real.sqrt h : ℂ)) *
          (((properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) -
            properTimeRadialCoefficient b (bridgeTime b E r)) / Real.sqrt h : ℝ) : ℂ))
        ((δ / (Real.sqrt h : ℂ)) ^ 2 *
          (properTimeRadialCoefficient b (bridgeTime b E r + Real.sqrt h * u) : ℂ)) using 1
      simp only [Complex.norm_mul, norm_pow]
    _ ≤ (2 * r * 1) * (L * |u|) + 1 ^ 2 * Q := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr]
      gcongr
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hquot
    _ = _ := by ring

theorem exists_eventually_radialCoefficient_lipschitz
    {ι : Type*} {l : Filter ι} {a τ : ι → ℝ} {b a₀ : ℝ}
    (hb : 0 < b) (ha₀ : 0 < a₀) (ha : Tendsto a l (𝓝 a₀))
    (hτ : Tendsto τ l (𝓝 a₀)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in l,
      |properTimeRadialCoefficient b (τ i) - properTimeRadialCoefficient b (a i)| ≤
        C * |τ i - a i| := by
  obtain ⟨C, S, hS, hLip⟩ :=
    (contDiffAt_properTimeRadialCoefficient hb ha₀ 1).exists_lipschitzOnWith
  refine ⟨C, C.coe_nonneg, ?_⟩
  filter_upwards [ha.eventually hS, hτ.eventually hS] with i hi hti
  simpa only [Real.dist_eq] using hLip.dist_le_mul (τ i) hti (a i) hi

/-- The complex residual tends to zero after division by `h`, without any
assumption on the rate at which the real energy or radius converges. -/
theorem tendsto_complexLandauPhaseRemainder_div
    {ι : Type*} {l : Filter ι} {h E r : ι → ℝ} {δ : ι → ℂ} {b E₀ r₀ : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀))
    (hδ : Tendsto (fun i => δ i / (Real.sqrt (h i) : ℂ)) l (𝓝 0)) (u : ℝ) :
    Tendsto (fun i => complexLandauPhaseRemainder b (E i) (r i) (δ i)
      (bridgeTime b (E i) (r i) + Real.sqrt (h i) * u) / (h i : ℂ)) l (𝓝 0) := by
  let a := fun i => bridgeTime b (E i) (r i)
  let τ := fun i => a i + Real.sqrt (h i) * u
  let a₀ := bridgeTime b E₀ r₀
  have ha₀ : 0 < a₀ := bridgeTime_pos hb hE₀ hr₀
  have ha : Tendsto a l (𝓝 a₀) := tendsto_bridgeTime_parameters b hE₀ hE hr
  have hroot : Tendsto (fun i => Real.sqrt (h i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (hh.mono_right nhdsWithin_le_nhds)
  have hτ : Tendsto τ l (𝓝 a₀) := by
    simpa only [zero_mul, add_zero] using ha.add (hroot.mul_const u)
  obtain ⟨C, hC, hLip⟩ := exists_eventually_radialCoefficient_lipschitz hb ha₀ ha hτ
  let dq := fun i => ((properTimeRadialCoefficient b (τ i) -
    properTimeRadialCoefficient b (a i)) / Real.sqrt (h i) : ℝ)
  have hdq : ∀ᶠ i in l, ‖(dq i : ℂ)‖ ≤ C * |u| := by
    filter_upwards [hLip, hh.eventually self_mem_nhdsWithin] with i hi hhi
    have hp : 0 < h i := hhi
    have hs : 0 < Real.sqrt (h i) := Real.sqrt_pos.mpr hp
    simp only [dq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    have ht : |τ i - a i| = Real.sqrt (h i) * |u| := by
      simp only [τ, add_sub_cancel_left, abs_mul, abs_of_pos hs]
    rw [ht] at hi
    nlinarith only [hi]
  have hrC : Tendsto (fun i => (r i : ℂ)) l (𝓝 (r₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hfirst : Tendsto (fun i => 2 * (r i : ℂ) *
      (δ i / (Real.sqrt (h i) : ℂ))) l (𝓝 0) := by
    simpa only [mul_zero] using (hrC.const_mul 2).mul hδ
  have hfirstprod : Tendsto (fun i => 2 * (r i : ℂ) *
      (δ i / (Real.sqrt (h i) : ℂ)) * (dq i : ℂ)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun i => ‖2 * (r i : ℂ) *
        (δ i / (Real.sqrt (h i) : ℂ))‖ * (C * |u|)) l (𝓝 0) by
          simpa only [norm_zero, zero_mul] using hfirst.norm.mul_const (C * |u|))
    filter_upwards [hdq] with i hi
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
  have hq : Tendsto (fun i => (properTimeRadialCoefficient b (τ i) : ℂ)) l
      (𝓝 (properTimeRadialCoefficient b a₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((contDiffAt_properTimeRadialCoefficient hb ha₀ 1).continuousAt.tendsto.comp hτ)
  have hsecond := (hδ.pow 2).mul hq
  have hsum : Tendsto (fun i => 2 * (r i : ℂ) *
      (δ i / (Real.sqrt (h i) : ℂ)) * (dq i : ℂ) +
      (δ i / (Real.sqrt (h i) : ℂ)) ^ 2 * (properTimeRadialCoefficient b (τ i) : ℂ))
      l (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero] using
      hfirstprod.add hsecond
  apply hsum.congr'
  filter_upwards [hh.eventually self_mem_nhdsWithin] with i hi
  have hp : 0 < h i := hi
  have hs : (Real.sqrt (h i) : ℂ) ^ 2 = (h i : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  change _ = complexLandauPhaseRemainder b (E i) (r i) (δ i) (τ i) / (h i : ℂ)
  unfold complexLandauPhaseRemainder
  dsimp only [dq]
  push_cast
  rw [← hs]
  ring

theorem tendsto_complexLandauLocalProfile_parameters
    {ι : Type*} {l : Filter ι} {h E r : ι → ℝ} {δ : ι → ℂ} {b E₀ r₀ ε : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀) (hε : 0 < ε)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀))
    (hδ : Tendsto (fun i => δ i / (Real.sqrt (h i) : ℂ)) l (𝓝 0)) (u : ℝ) :
    Tendsto (fun i => complexLandauLocalProfile b (E i) (r i) ε (h i) (δ i) u) l
      (𝓝 (((Real.sinh (b * bridgeTime b E₀ r₀))⁻¹ *
        Real.exp (-(properTimeHessian b E₀ r₀ / 2) * u ^ 2) : ℝ) : ℂ)) := by
  have hreal := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_landauLocalProfile_parameters hb hE₀ hr₀ hε hh hE hr u)
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (tendsto_complexLandauPhaseRemainder_div hb hE₀ hr₀ hh hE hr hδ u).neg
  simpa only [complexLandauLocalProfile, neg_div, neg_zero, Complex.exp_zero, mul_one] using
    hreal.mul he

/-- A single integrable Gaussian bounds the whole local complex profile on
a positive parameter rectangle, whenever `‖δ / sqrt h‖ ≤ 1`. -/
theorem exists_complexLandauLocalProfile_uniform_gaussian
    {b Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hrmin : 0 < rmin)
    (hrmax : rmin ≤ rmax)
    (hε : 0 < ε) (hεa : ε < bridgeTime b Emax rmin) :
    ∃ B m : ℝ, 0 < B ∧ 0 < m ∧ ∀ (E r h : ℝ) (δ : ℂ),
      E ∈ Icc Emin Emax → r ∈ Icc rmin rmax → 0 < h →
      ‖δ / (Real.sqrt h : ℂ)‖ ≤ 1 → ∀ u : ℝ,
      ‖complexLandauLocalProfile b E r ε h δ u‖ ≤ B * Real.exp (-m * u ^ 2) := by
  let tmin := bridgeTime b Emax rmin - ε
  let tmax := bridgeTime b Emin rmax + ε
  let m := properTimeHessianFloor b rmin tmax
  let A := (Real.sinh (b * tmin))⁻¹
  have htmin : 0 < tmin := sub_pos.mpr hεa
  have htmax : 0 < tmax := add_pos (bridgeTime_pos hb hEmin (hrmin.trans_le hrmax)) hε
  have hm : 0 < m := properTimeHessianFloor_pos hb hrmin htmax
  have hA : 0 < A := inv_pos.mpr (Real.sinh_pos_iff.mpr (mul_pos hb htmin))
  have hqC : ContDiffOn ℝ 1 (properTimeRadialCoefficient b) (Icc tmin tmax) :=
    fun τ hτ => (contDiffAt_properTimeRadialCoefficient hb (htmin.trans_le hτ.1) 1).contDiffWithinAt
  obtain ⟨K, hK⟩ := hqC.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  obtain ⟨Q₀, hQ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hqC.continuousOn
  let Q := max Q₀ 0
  let L := 2 * rmax * (K : ℝ)
  have hrmaxpos : 0 < rmax := hrmin.trans_le hrmax
  have hQ : 0 ≤ Q := le_max_right _ _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨A * Real.exp (Q + L ^ 2 / m), m / 4, by positivity, by positivity,
    fun E r h δ hiE hir hh hδ u => ?_⟩
  let a := bridgeTime b E r
  let τ := a + Real.sqrt h * u
  have hbox := bridgeTime_mem_uniform_Icc hb hEmin hrmin hiE hir
  have ha : a ∈ Icc tmin tmax := by
    constructor <;> dsimp [a, tmin, tmax] <;> linarith [hbox.1, hbox.2]
  by_cases hmem : τ ∈ Ioo (a - ε) (a + ε)
  · have hτ : τ ∈ Icc tmin tmax := by
      constructor <;> dsimp [tmin, tmax] <;> linarith [hbox.1, hbox.2, hmem.1, hmem.2]
    have hlip : |properTimeRadialCoefficient b τ - properTimeRadialCoefficient b a| ≤
        (K : ℝ) * |Real.sqrt h * u| := by
      simpa only [Real.dist_eq, τ, add_sub_cancel_left] using hK.dist_le_mul τ hτ a ha
    have hq : |properTimeRadialCoefficient b τ| ≤ Q := by
      have hx : |properTimeRadialCoefficient b τ| ≤ Q₀ := by
        simpa only [Real.norm_eq_abs] using hQ₀ τ hτ
      exact hx.trans (le_max_left _ _)
    have hrem := norm_complexLandauPhaseRemainder_div_le hh
      (hrmin.trans_le hir.1).le δ u hδ hlip hq
    have hrem' : ‖complexLandauPhaseRemainder b E r δ τ / (h : ℂ)‖ ≤ L * |u| + Q := by
      apply hrem.trans
      dsimp only [L]
      gcongr
      exact hir.2
    have hexp : ‖Complex.exp (-complexLandauPhaseRemainder b E r δ τ / (h : ℂ))‖ ≤
        Real.exp (L * |u| + Q) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      apply (Complex.re_le_norm _).trans
      simpa only [neg_div, norm_neg] using hrem'
    have hreal : ‖landauLocalProfile b E r ε h u‖ ≤ A * Real.exp (-(m / 2) * u ^ 2) :=
      norm_landauLocalProfile_uniform_le hb hEmin hrmin hiE hir hε hεa hh u
    have hyoung : L * |u| ≤ m / 4 * u ^ 2 + L ^ 2 / m := by
      apply (mul_le_mul_iff_right₀ hm).mp
      have hs := sq_nonneg (m * |u| - 2 * L)
      rw [mul_add, mul_div_cancel₀ _ hm.ne']
      simp only [sub_sq, mul_pow, sq_abs] at hs
      nlinarith only [hs]
    calc
      _ = ‖landauLocalProfile b E r ε h u‖ *
          ‖Complex.exp (-complexLandauPhaseRemainder b E r δ τ / (h : ℂ))‖ := by
        simp only [complexLandauLocalProfile, norm_mul, Complex.norm_real]
        rfl
      _ ≤ (A * Real.exp (-(m / 2) * u ^ 2)) * Real.exp (L * |u| + Q) :=
        mul_le_mul hreal hexp (norm_nonneg _) (by positivity)
      _ = A * Real.exp (-(m / 2) * u ^ 2 + (L * |u| + Q)) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ A * Real.exp ((Q + L ^ 2 / m) + (-(m / 4) * u ^ 2)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA.le
        linarith
      _ = _ := by rw [Real.exp_add, mul_assoc]
  · have hmem' : a + Real.sqrt h * u ∉ Ioo (a - ε) (a + ε) := hmem
    dsimp only [a] at hmem'
    simp only [complexLandauLocalProfile, landauLocalProfile,
      indicator_of_notMem hmem', Complex.ofReal_zero, zero_mul, norm_zero]
    positivity

/-- Dominated convergence for the true local complex profile. -/
theorem tendsto_integral_complexLandauLocalProfile_parameters
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {δ : ι → ℂ} {b E₀ r₀ Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hEmin : 0 < Emin) (hrmin : 0 < rmin)
    (hrmax : rmin ≤ rmax)
    (hε : 0 < ε) (hεa : ε < bridgeTime b Emax rmin)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀))
    (hδ : Tendsto (fun i => δ i / (Real.sqrt (h i) : ℂ)) l (𝓝 0))
    (hEbox : ∀ᶠ i in l, E i ∈ Icc Emin Emax) (hrbox : ∀ᶠ i in l, r i ∈ Icc rmin rmax) :
    Tendsto (fun i => ∫ u : ℝ, complexLandauLocalProfile b (E i) (r i) ε (h i) (δ i) u) l
      (𝓝 (((Real.sinh (b * bridgeTime b E₀ r₀))⁻¹ *
        Real.sqrt (2 * Real.pi / properTimeHessian b E₀ r₀) : ℝ) : ℂ)) := by
  obtain ⟨B, m, hB, hm, hmajor⟩ :=
    exists_complexLandauLocalProfile_uniform_gaussian hb hEmin hrmin hrmax hε hεa
  have hsmall : ∀ᶠ i in l, ‖δ i / (Real.sqrt (h i) : ℂ)‖ ≤ 1 :=
    (show Tendsto (fun i => ‖δ i / (Real.sqrt (h i) : ℂ)‖) l (𝓝 0) by
      simpa only [norm_zero] using hδ.norm).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (fun u : ℝ => B * Real.exp (-m * u ^ 2))
    (Eventually.of_forall fun i =>
      (measurable_complexLandauLocalProfile b (E i) (r i) ε (h i) (δ i)).aestronglyMeasurable)
    (show ∀ᶠ i in l, ∀ᵐ u : ℝ, ‖complexLandauLocalProfile b (E i) (r i) ε (h i) (δ i) u‖ ≤
        B * Real.exp (-m * u ^ 2) from by
      filter_upwards [hEbox, hrbox, hh.eventually self_mem_nhdsWithin, hsmall] with i hiE hir hih hiδ
      exact Eventually.of_forall (hmajor (E i) (r i) (h i) (δ i) hiE hir hih hiδ))
    ((integrable_exp_neg_mul_sq hm).const_mul B)
    (Eventually.of_forall (tendsto_complexLandauLocalProfile_parameters hb hE₀ hr₀ hε hh hE hr hδ))
  convert hlim using 1
  rw [integral_complex_ofReal, integral_const_mul, integral_gaussian]
  congr 3
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring_nf

end InfiniteZero
