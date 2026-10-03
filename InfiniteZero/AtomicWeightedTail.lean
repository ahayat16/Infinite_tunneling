import InfiniteZero.AtomicGroundAgmon
import InfiniteZero.AtomicPerturbationDomain

/-!
# Bounded exponential weights on the radial atomic state

A continuous nonnegative bounded weight supported beyond `4 r₀` changes
the radial ground state by an exponentially small L² vector. The allowed
weight strength ranges over a fixed interval, independently of the coupling.
This result uses no derivative of the weight and no assertion about a form
or operator domain.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

theorem abs_atomicExponentialWeight_le {T : Plane → ℝ} {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) (x : Plane) :
    |Real.exp (κ * coupling * T x)| ≤ Real.exp (|κ * coupling| * M) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right (le_abs_self _) (hT x).1).trans
    (mul_le_mul_of_nonneg_left (hT x).2 (abs_nonneg _))

theorem abs_atomicExponentialWeightDefect_le {T : Plane → ℝ} {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) (x : Plane) :
    |Real.exp (κ * coupling * T x) - 1| ≤ Real.exp (|κ * coupling| * M) + 1 := by
  exact (abs_sub _ _).trans (add_le_add (abs_atomicExponentialWeight_le hT coupling κ x)
    (by simp))

/-- Actual multiplication by `exp (κ λ T)` on complex physical L². -/
def atomicExponentialWeightMul (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) : L2Space →L[ℂ] L2Space :=
  boundedPotentialMul (fun x => Real.exp (κ * coupling * T x))
    (by fun_prop) (abs_atomicExponentialWeight_le hT coupling κ)

/-- Actual multiplication by `exp (κ λ T) - 1`. -/
def atomicExponentialWeightDefectMul (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) : L2Space →L[ℂ] L2Space :=
  boundedPotentialMul (fun x => Real.exp (κ * coupling * T x) - 1)
    (by fun_prop)
    (abs_atomicExponentialWeightDefect_le hT coupling κ)

theorem coe_atomicExponentialWeightMul (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) (u : L2Space) :
    atomicExponentialWeightMul T hTc hT coupling κ u =ᵐ[volume]
      fun x => (Real.exp (κ * coupling * T x) : ℂ) * u x :=
  coe_boundedPotentialMul _ _ _ u

theorem coe_atomicExponentialWeightDefectMul (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) (u : L2Space) :
    atomicExponentialWeightDefectMul T hTc hT coupling κ u =ᵐ[volume]
      fun x => ((Real.exp (κ * coupling * T x) - 1 : ℝ) : ℂ) * u x :=
  coe_boundedPotentialMul _ _ _ u

theorem atomicExponentialWeightMul_apply_eq_add (T : Plane → ℝ) (hTc : Continuous T)
    {M : ℝ} (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) (u : L2Space) :
    atomicExponentialWeightMul T hTc hT coupling κ u =
      u + atomicExponentialWeightDefectMul T hTc hT coupling κ u := by
  apply Lp.ext
  filter_upwards [coe_atomicExponentialWeightMul T hTc hT coupling κ u,
    coe_atomicExponentialWeightDefectMul T hTc hT coupling κ u,
    Lp.coeFn_add u (atomicExponentialWeightDefectMul T hTc hT coupling κ u)] with x hw hd ha
  rw [hw, ha, Pi.add_apply, hd]
  push_cast
  ring

/-- Squared defect norm is controlled by the actual exterior probability. -/
theorem norm_atomicExponentialWeightDefectMul_sq_le_tail
    (T : Plane → ℝ) (hTc : Continuous T) {M R : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (hzero : ∀ x, ‖x‖ ≤ R → T x = 0)
    {coupling κ : ℝ} (hc : 0 ≤ coupling) (hκ : 0 ≤ κ)
    {u : L2Space} {φ : Wavefunction} (hu : Represents u φ) :
    ‖atomicExponentialWeightDefectMul T hTc hT coupling κ u‖ ^ 2 ≤
      Real.exp (κ * coupling * M) ^ 2 * ∫ x in {x : Plane | R ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  let D := atomicExponentialWeightDefectMul T hTc hT coupling κ u
  let S : Set Plane := {x | R ≤ ‖x‖}
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  have hrep : Represents D (fun x => ((Real.exp (κ * coupling * T x) - 1 : ℝ) : ℂ) * φ x) := by
    filter_upwards [coe_atomicExponentialWeightDefectMul T hTc hT coupling κ u, hu] with x hd hx
    change D x = _
    change D x = _ at hd
    rw [hd, hx]
  have hcap (x : Plane) : |Real.exp (κ * coupling * T x) - 1| ≤
      Real.exp (κ * coupling * M) := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr
      (mul_nonneg (mul_nonneg hκ hc) (hT x).1)))]
    exact (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hT x).2 (mul_nonneg hκ hc)))
  rw [hrep.norm_sq_eq_mass]
  calc
    mass (fun x => ((Real.exp (κ * coupling * T x) - 1 : ℝ) : ℂ) * φ x) ≤
        ∫ x : Plane, S.indicator (fun x => Real.exp (κ * coupling * M) ^ 2 * ‖φ x‖ ^ 2) x := by
      apply integral_mono hrep.memLp.norm.integrable_sq
        ((hu.memLp.norm.integrable_sq.const_mul _).indicator hS)
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        change ‖((Real.exp (κ * coupling * T x) - 1 : ℝ) : ℂ) * φ x‖ ^ 2 ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (abs_nonneg _) (Real.exp_pos _).le).mpr (hcap x)) (sq_nonneg _)
      · have hn : ‖x‖ ≤ R := (lt_of_not_ge hx).le
        simp only [indicator_of_notMem hx, hzero x hn, mul_zero, Real.exp_zero,
          sub_self, Complex.ofReal_zero, zero_mul, norm_zero,
          zero_pow (by norm_num : 2 ≠ 0), le_refl]
    _ = _ := by rw [integral_indicator hS, integral_const_mul]

namespace CuspParameters

/-- Uniformly weak exponential weights change every normalized radial-core
ground state by an exponentially small amount. Only continuity, bounds and
the stated support condition on the weight are used. -/
theorem exists_atomicWeightedTail_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ x, T x ∈ Icc 0 M)
    (hzero : ∀ x, ‖x‖ ≤ 4 * p.r₀ → T x = 0) :
    ∃ κ₀ > 0, ∃ c > 0, ∃ C > 0, ∃ N > 0,
      ∀ coupling : ℝ, N ≤ coupling → ∀ κ ∈ Icc 0 κ₀,
        ∀ φ, IsAtomicGroundState p.b p.core coupling φ →
          ∀ u : L2Space, Represents u φ →
            ‖atomicExponentialWeightDefectMul T hTc hT coupling κ u‖ ≤
              C * Real.exp (-c * coupling) ∧
            ‖atomicExponentialWeightMul T hTc hT coupling κ u‖ ≤
              1 + C * Real.exp (-c * coupling) := by
  obtain ⟨C, hC, d, hd, N, hN, htail⟩ :=
    exists_atomicGround_agmon_tail_of_radialData hp hRad hAcore hApot
  let κ₀ := d / (2 * (M + 1))
  have hden : 0 < 2 * (M + 1) := by positivity
  have hκ₀ : 0 < κ₀ := div_pos hd hden
  refine ⟨κ₀, hκ₀, d / 2, half_pos hd, Real.sqrt C, Real.sqrt_pos.mpr hC,
    max N 1, hN.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc κ hκ φ hφ u hu
  have hcN : N ≤ coupling := (le_max_left N 1).trans hc
  have hc1 : 1 ≤ coupling := (le_max_right N 1).trans hc
  have hcpos : 0 < coupling := lt_of_lt_of_le zero_lt_one hc1
  have hκM : κ * M ≤ d / 2 := by
    have hratio : κ₀ * (M + 1) = d / 2 := by dsimp only [κ₀]; field_simp
    have hm := mul_le_mul_of_nonneg_right hκ.2 hM
    nlinarith only [hm, hratio, hκ₀.le]
  have hmass := (htail coupling hcN).2.2 φ hφ
  have hsquare := (norm_atomicExponentialWeightDefectMul_sq_le_tail T hTc hT hzero
    hcpos.le hκ.1 hu).trans
      (mul_le_mul_of_nonneg_left hmass (sq_nonneg (Real.exp (κ * coupling * M))))
  have hprod : Real.exp (κ * coupling * M) ^ 2 *
      ((C / coupling ^ 2) * Real.exp (-2 * d * coupling)) =
      (C / coupling ^ 2) * Real.exp ((2 * κ * M - 2 * d) * coupling) := by
    rw [pow_two]
    calc
      _ = (C / coupling ^ 2) *
          (Real.exp (κ * coupling * M) * Real.exp (κ * coupling * M) *
            Real.exp (-2 * d * coupling)) := by ring
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hdiv : C / coupling ^ 2 ≤ C := by
    apply (div_le_iff₀ (sq_pos_of_pos hcpos)).mpr
    have hs : 1 ≤ coupling ^ 2 := by nlinarith only [hc1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hC.le
  have hexp : Real.exp ((2 * κ * M - 2 * d) * coupling) ≤ Real.exp (-d * coupling) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith only [hκM]) hcpos.le
  have hfinal : ‖atomicExponentialWeightDefectMul T hTc hT coupling κ u‖ ^ 2 ≤
      C * Real.exp (-d * coupling) := by
    rw [hprod] at hsquare
    exact hsquare.trans (mul_le_mul hdiv hexp (Real.exp_pos _).le hC.le)
  have hrhs : (Real.sqrt C * Real.exp (-(d / 2) * coupling)) ^ 2 =
      C * Real.exp (-d * coupling) := by
    rw [mul_pow, Real.sq_sqrt hC.le, pow_two, ← Real.exp_add]
    congr 2
    ring
  have hnorm : ‖atomicExponentialWeightDefectMul T hTc hT coupling κ u‖ ≤
      Real.sqrt C * Real.exp (-(d / 2) * coupling) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)).mp
    rwa [hrhs]
  have hunorm : ‖u‖ = 1 := by
    have hs := hu.norm_sq_eq_mass.trans hφ.2
    nlinarith [norm_nonneg u]
  refine ⟨hnorm, ?_⟩
  rw [atomicExponentialWeightMul_apply_eq_add]
  exact (norm_add_le _ _).trans (by rw [hunorm]; exact add_le_add le_rfl hnorm)

end CuspParameters
end InfiniteZero
