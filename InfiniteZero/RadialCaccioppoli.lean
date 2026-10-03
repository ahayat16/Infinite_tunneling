import InfiniteZero.RadialWronskian
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A finite-interval radial Caccioppoli estimate

For a real solution of `f'' = q f - f'/r` with nonnegative `q`, multiplying
by a compactly supported cutoff gives a derivative estimate. All integrability
facts below follow from continuity on the finite interval; no finite-energy
assumption on the solution or its derivative is used.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- The flux obtained by multiplying the radial equation by `χ² f`. -/
def radialCutoffFlux (f df χ : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * χ r ^ 2 * f r * df r

/-- Its derivative after substituting the radial equation. -/
def radialCutoffFluxDerivative (q f df χ dχ : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * χ r ^ 2 * df r ^ 2 + r * q r * χ r ^ 2 * f r ^ 2 +
    2 * r * χ r * dχ r * f r * df r

theorem hasDerivAt_radialCutoffFlux {a r : ℝ} {q f df χ dχ : ℝ → ℝ}
    (ha : 0 < a) (hf : IsRadialODESolutionOn q f df a) (hr : a < r)
    (hχ : HasDerivAt χ (dχ r) r) :
    HasDerivAt (radialCutoffFlux f df χ)
      (radialCutoffFluxDerivative q f df χ dχ r) r := by
  have hrpos : 0 < r := ha.trans hr
  have hd := ((((hasDerivAt_id r).mul (hχ.pow 2)).mul
    (hf.deriv r hr)).mul (hf.second r hr))
  convert hd using 1
  simp only [radialCutoffFluxDerivative, Pi.mul_apply, Pi.pow_apply,
    id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hrpos.ne']
  ring

private theorem radial_cutoff_continuities {a l u : ℝ} {q f df χ dχ : ℝ → ℝ}
    (hf : IsRadialODESolutionOn q f df a) (hal : a < l)
    (hχ : ∀ r ∈ Icc l u, HasDerivAt χ (dχ r) r) :
    ContinuousOn f (Icc l u) ∧ ContinuousOn df (Icc l u) ∧
      ContinuousOn χ (Icc l u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (hf.deriv r (hal.trans_le hr.1)).continuousAt.continuousWithinAt
  · intro r hr
    exact (hf.second r (hal.trans_le hr.1)).continuousAt.continuousWithinAt
  · intro r hr
    exact (hχ r hr).continuousAt.continuousWithinAt

private theorem continuousOn_radialCutoffFluxDerivative {l u : ℝ}
    {q f df χ dχ : ℝ → ℝ}
    (hq : ContinuousOn q (Icc l u)) (hf : ContinuousOn f (Icc l u))
    (hdf : ContinuousOn df (Icc l u)) (hχ : ContinuousOn χ (Icc l u))
    (hdχ : ContinuousOn dχ (Icc l u)) :
    ContinuousOn (radialCutoffFluxDerivative q f df χ dχ) (Icc l u) := by
  unfold radialCutoffFluxDerivative
  exact (((continuousOn_id.mul (hχ.pow 2)).mul (hdf.pow 2)).add
    (((continuousOn_id.mul hq).mul (hχ.pow 2)).mul (hf.pow 2))).add
      (((((continuousOn_const.mul continuousOn_id).mul hχ).mul hdχ).mul hf).mul hdf)

/-- There is no boundary flux when the cutoff vanishes at both endpoints. -/
theorem integral_radialCutoffFluxDerivative_eq_zero {a l u : ℝ}
    {q f df χ dχ : ℝ → ℝ}
    (ha : 0 < a) (hf : IsRadialODESolutionOn q f df a)
    (hal : a < l) (hlu : l ≤ u)
    (hq : ContinuousOn q (Icc l u))
    (hχ : ∀ r ∈ Icc l u, HasDerivAt χ (dχ r) r)
    (hdχ : ContinuousOn dχ (Icc l u)) (hχl : χ l = 0) (hχu : χ u = 0) :
    (∫ r in l..u, radialCutoffFluxDerivative q f df χ dχ r) = 0 := by
  obtain ⟨hfc, hdfc, hχc⟩ := radial_cutoff_continuities hf hal hχ
  have hD := continuousOn_radialCutoffFluxDerivative hq hfc hdfc hχc hdχ
  have hi : IntervalIntegrable (radialCutoffFluxDerivative q f df χ dχ) volume l u :=
    hD.intervalIntegrable_of_Icc hlu
  have hderiv : ∀ r ∈ Ioo l u, HasDerivAt (radialCutoffFlux f df χ)
      (radialCutoffFluxDerivative q f df χ dχ r) r := by
    intro r hr
    exact hasDerivAt_radialCutoffFlux ha hf (hal.trans hr.1) (hχ r ⟨hr.1.le, hr.2.le⟩)
  have hc : ContinuousOn (radialCutoffFlux f df χ) (Icc l u) :=
    ((continuousOn_id.mul (hχc.pow 2)).mul hfc).mul hdfc
  simpa [radialCutoffFlux, hχl, hχu] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlu hc hderiv hi

/-- The elementary completed-square bound used by the radial energy estimate. -/
theorem radial_caccioppoli_pointwise {q f df χ dχ : ℝ → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hq : 0 ≤ q r) :
    r * χ r ^ 2 * df r ^ 2 ≤
      2 * radialCutoffFluxDerivative q f df χ dχ r +
        4 * (r * dχ r ^ 2 * f r ^ 2) := by
  unfold radialCutoffFluxDerivative
  nlinarith [mul_nonneg hr (sq_nonneg (χ r * df r + 2 * dχ r * f r)),
    mul_nonneg (mul_nonneg hr hq) (sq_nonneg (χ r * f r))]

/-- A radial Caccioppoli inequality on a finite interval. The cutoff and its
derivative need only satisfy the displayed local regularity conditions. -/
theorem radial_caccioppoli {a l u : ℝ} {q f df χ dχ : ℝ → ℝ}
    (ha : 0 < a) (hf : IsRadialODESolutionOn q f df a)
    (hal : a < l) (hlu : l ≤ u)
    (hq : ContinuousOn q (Icc l u)) (hq_nonneg : ∀ r ∈ Icc l u, 0 ≤ q r)
    (hχ : ∀ r ∈ Icc l u, HasDerivAt χ (dχ r) r)
    (hdχ : ContinuousOn dχ (Icc l u)) (hχl : χ l = 0) (hχu : χ u = 0) :
    (∫ r in l..u, r * χ r ^ 2 * df r ^ 2) ≤
      4 * ∫ r in l..u, r * dχ r ^ 2 * f r ^ 2 := by
  obtain ⟨hfc, hdfc, hχc⟩ := radial_cutoff_continuities hf hal hχ
  have hXi : IntervalIntegrable (fun r => r * χ r ^ 2 * df r ^ 2) volume l u :=
    ((continuousOn_id.mul (hχc.pow 2)).mul (hdfc.pow 2)).intervalIntegrable_of_Icc hlu
  have hYi : IntervalIntegrable (fun r => r * dχ r ^ 2 * f r ^ 2) volume l u :=
    ((continuousOn_id.mul (hdχ.pow 2)).mul (hfc.pow 2)).intervalIntegrable_of_Icc hlu
  have hDi : IntervalIntegrable (radialCutoffFluxDerivative q f df χ dχ) volume l u :=
    (continuousOn_radialCutoffFluxDerivative hq hfc hdfc hχc hdχ).intervalIntegrable_of_Icc hlu
  have hzero := integral_radialCutoffFluxDerivative_eq_zero ha hf hal hlu hq hχ hdχ hχl hχu
  have hle := intervalIntegral.integral_mono_on hlu hXi
    ((hDi.const_mul 2).add (hYi.const_mul 4)) (fun r hr =>
      radial_caccioppoli_pointwise (ha.le.trans ((hal.le).trans hr.1)) (hq_nonneg r hr))
  rwa [intervalIntegral.integral_add (hDi.const_mul 2) (hYi.const_mul 4),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hzero, mul_zero, zero_add] at hle

end InfiniteZero
