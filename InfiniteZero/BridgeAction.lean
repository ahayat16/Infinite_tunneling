import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The real bridge action

The explicit formula is that of P2.2 in the blueprint. This file establishes its
real-variable calculus. Identifying it with the minimum of the proper-time phase,
or with the exponential rate of the Landau resolvent, is a separate task.
-/

noncomputable section
open Set
open scoped Topology

namespace InfiniteZero

/-- The explicit real bridge action, extended to all real radii by the same formula. -/
def bridgeAction (b E r : ℝ) : ℝ :=
  r / 4 * Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) +
    E / b * Real.arsinh (b * r / (2 * Real.sqrt E))

/-- The positive proper time predicted by the stationary point equation. -/
def bridgeTime (b E r : ℝ) : ℝ :=
  Real.arsinh (b * r / (2 * Real.sqrt E)) / b

@[simp] theorem bridgeAction_zero (b E : ℝ) : bridgeAction b E 0 = 0 := by
  simp [bridgeAction]

theorem bridgeTime_pos {b E r : ℝ} (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    0 < bridgeTime b E r := by
  apply div_pos _ hb
  rw [Real.arsinh_pos_iff]
  exact div_pos (mul_pos hb hr) (mul_pos (by norm_num) (Real.sqrt_pos.2 hE))

theorem sinh_bridgeTime {b : ℝ} (hb : b ≠ 0) (E r : ℝ) :
    Real.sinh (b * bridgeTime b E r) = b * r / (2 * Real.sqrt E) := by
  simp [bridgeTime, mul_div_cancel₀ _ hb]

private theorem action_radicand_pos (b r : ℝ) {E : ℝ} (hE : 0 < E) :
    0 < b ^ 2 * r ^ 2 + 4 * E := by positivity

private theorem action_sqrt_rescale (b r : ℝ) {E : ℝ} (hE : 0 < E) :
    Real.sqrt (1 + (b * r / (2 * Real.sqrt E)) ^ 2) =
      Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) / (2 * Real.sqrt E) := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hs2 := Real.sq_sqrt hE.le
  have hA := Real.sq_sqrt (action_radicand_pos b r hE).le
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  field_simp
  nlinarith

theorem hasDerivAt_bridgeAction {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    HasDerivAt (bridgeAction b E) (Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) / 2) r := by
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hA : 0 < Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) :=
    Real.sqrt_pos.2 (action_radicand_pos b r hE)
  have hrad := (((hasDerivAt_id r).pow 2).const_mul (b ^ 2)).add_const (4 * E)
  have hroot := hrad.sqrt (ne_of_gt (action_radicand_pos b r hE))
  have hfirst := ((hasDerivAt_id r).div_const 4).mul hroot
  have hsecond := (((hasDerivAt_id r).const_mul b).div_const
    (2 * Real.sqrt E)).arsinh.const_mul (E / b)
  convert hfirst.add hsecond using 1
  simp only [id, Pi.pow_apply, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    mul_one]
  rw [action_sqrt_rescale b r hE]
  have hs2 := Real.sq_sqrt hE.le
  have hA2 := Real.sq_sqrt (action_radicand_pos b r hE).le
  field_simp
  nlinarith

theorem deriv_bridgeAction {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    deriv (bridgeAction b E) r = Real.sqrt (b ^ 2 * r ^ 2 + 4 * E) / 2 :=
  (hasDerivAt_bridgeAction hb hE r).deriv

theorem differentiable_bridgeAction {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) :
    Differentiable ℝ (bridgeAction b E) :=
  fun r => (hasDerivAt_bridgeAction hb hE r).differentiableAt

theorem continuous_bridgeAction {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) :
    Continuous (bridgeAction b E) :=
  (differentiable_bridgeAction hb hE).continuous

theorem bridgeAction_eikonal {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    deriv (bridgeAction b E) r ^ 2 = E + b ^ 2 * r ^ 2 / 4 := by
  rw [deriv_bridgeAction hb hE, div_pow, Real.sq_sqrt (action_radicand_pos b r hE).le]
  ring

theorem deriv_bridgeAction_pos {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    0 < deriv (bridgeAction b E) r := by
  rw [deriv_bridgeAction hb hE]
  exact div_pos (Real.sqrt_pos.2 (action_radicand_pos b r hE)) (by norm_num)

theorem strictMono_bridgeAction {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) :
    StrictMono (bridgeAction b E) :=
  strictMono_of_deriv_pos (deriv_bridgeAction_pos hb hE)

theorem bridgeAction_pos {b E r : ℝ} (hb : b ≠ 0) (hE : 0 < E) (hr : 0 < r) :
    0 < bridgeAction b E r := by
  simpa only [bridgeAction_zero] using (strictMono_bridgeAction hb hE) hr

theorem sqrt_energy_le_deriv_bridgeAction {b E : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    Real.sqrt E ≤ deriv (bridgeAction b E) r := by
  have hderiv := deriv_bridgeAction_pos hb hE r
  have heik := bridgeAction_eikonal hb hE r
  have hs := Real.sq_sqrt hE.le
  have hp : 0 ≤ b ^ 2 * r ^ 2 / 4 := by positivity
  nlinarith [Real.sqrt_nonneg E]

/-- The linear action gain used when the bridge length increases in the cusp. -/
theorem bridgeAction_sub_ge {b E s r : ℝ} (hb : b ≠ 0) (hE : 0 < E) (hsr : s ≤ r) :
    Real.sqrt E * (r - s) ≤ bridgeAction b E r - bridgeAction b E s :=
  mul_sub_le_image_sub_of_le_deriv (differentiable_bridgeAction hb hE)
    (sqrt_energy_le_deriv_bridgeAction hb hE) hsr

theorem bridgeAction_ge_sqrt_energy_mul {b E r : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hr : 0 ≤ r) :
    Real.sqrt E * r ≤ bridgeAction b E r := by
  simpa only [sub_zero, bridgeAction_zero] using bridgeAction_sub_ge hb hE hr

theorem hasDerivAt_deriv_bridgeAction {b E : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    HasDerivAt (deriv (bridgeAction b E))
      (b ^ 2 * r / (2 * Real.sqrt (b ^ 2 * r ^ 2 + 4 * E))) r := by
  have hrad := (((hasDerivAt_id r).pow 2).const_mul (b ^ 2)).add_const (4 * E)
  have hroot := (hrad.sqrt (ne_of_gt (action_radicand_pos b r hE))).div_const 2
  have hfun : deriv (bridgeAction b E) =
      fun x => Real.sqrt (b ^ 2 * x ^ 2 + 4 * E) / 2 :=
    funext (deriv_bridgeAction hb hE)
  rw [hfun]
  convert hroot using 1
  simp only [id, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

theorem deriv2_bridgeAction {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    deriv (deriv (bridgeAction b E)) r =
      b ^ 2 * r / (2 * Real.sqrt (b ^ 2 * r ^ 2 + 4 * E)) :=
  (hasDerivAt_deriv_bridgeAction hb hE r).deriv

theorem deriv2_bridgeAction_pos {b E r : ℝ}
    (hb : b ≠ 0) (hE : 0 < E) (hr : 0 < r) :
    0 < deriv (deriv (bridgeAction b E)) r := by
  rw [deriv2_bridgeAction hb hE]
  exact div_pos (mul_pos (sq_pos_of_ne_zero hb) hr)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (action_radicand_pos b r hE)))

theorem strictConvexOn_bridgeAction {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) :
    StrictConvexOn ℝ (Ici 0) (bridgeAction b E) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
    (continuous_bridgeAction hb hE).continuousOn
  intro r hr
  rw [interior_Ici] at hr
  exact deriv2_bridgeAction_pos hb hE hr

theorem deriv_bridgeAction_eq_sqrt {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    deriv (bridgeAction b E) r = Real.sqrt (E + b ^ 2 * r ^ 2 / 4) := by
  have hderiv := deriv_bridgeAction_pos hb hE r
  have heik := bridgeAction_eikonal hb hE r
  symm
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) hderiv.le).2 heik.symm

/-- The eikonal integral representation, with no restriction on the endpoint. -/
theorem bridgeAction_eq_integral {b E : ℝ} (hb : b ≠ 0) (hE : 0 < E) (r : ℝ) :
    bridgeAction b E r = ∫ s in (0 : ℝ)..r, Real.sqrt (E + b ^ 2 * s ^ 2 / 4) := by
  have hd (s : ℝ) : HasDerivAt (bridgeAction b E)
      (Real.sqrt (E + b ^ 2 * s ^ 2 / 4)) s := by
    rw [← deriv_bridgeAction_eq_sqrt hb hE s]
    exact (hasDerivAt_bridgeAction hb hE s).differentiableAt.hasDerivAt
  have hc : Continuous (fun s : ℝ => Real.sqrt (E + b ^ 2 * s ^ 2 / 4)) := by
    fun_prop
  simpa only [bridgeAction_zero, sub_zero] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hc.intervalIntegrable 0 r)).symm

theorem magnetic_slope_le_deriv_bridgeAction {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 ≤ r) :
    b * r / 2 ≤ deriv (bridgeAction b E) r := by
  have hd := deriv_bridgeAction_pos hb.ne' hE r
  have heik := bridgeAction_eikonal hb.ne' hE r
  have hbr : 0 ≤ b * r / 2 := by positivity
  nlinarith

/-- The quadratic action gain, used for the quantitative same-cusp margin. -/
theorem bridgeAction_sub_ge_quadratic {b E s r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hs : 0 ≤ s) (hsr : s ≤ r) :
    b / 4 * (r ^ 2 - s ^ 2) ≤ bridgeAction b E r - bridgeAction b E s := by
  let f : ℝ → ℝ := fun x => bridgeAction b E x - b * x ^ 2 / 4
  have hd (x : ℝ) : HasDerivAt f (deriv (bridgeAction b E) x - b * x / 2) x := by
    have hp := (((hasDerivAt_id x).pow 2).const_mul b).div_const 4
    convert ((differentiable_bridgeAction hb.ne' hE x).hasDerivAt).sub hp using 1
    simp only [id, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  have hdiff : Differentiable ℝ f := fun x => (hd x).differentiableAt
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro x hx
    rw [(hd x).deriv]
    exact sub_nonneg.mpr
      (magnetic_slope_le_deriv_bridgeAction hb hE (interior_subset hx))
  have h := hm hs (hs.trans hsr) hsr
  dsimp [f] at h
  nlinarith

end InfiniteZero
