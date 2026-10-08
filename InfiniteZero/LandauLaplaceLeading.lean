import InfiniteZero.LandauLaplaceTails
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The leading Laplace coefficient of the radial proper-time integral

The quadratic limit, a Gaussian majorant and dominated convergence prove the
localized asymptotic. The exact affine change of variables and the previously
proved tail estimate then give the leading coefficient of `landauKernel`.
This is a theorem about its defining scalar integral, without an operator
resolvent identity as an input.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def properTimeHessian (b E r : ℝ) : ℝ :=
  deriv (deriv (properTimePhase b E r)) (bridgeTime b E r)

theorem properTimeHessian_pos {b E r : ℝ} (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    0 < properTimeHessian b E r :=
  deriv2_properTimePhase_pos hb hr (bridgeTime_pos hb hE hr) E

theorem tendsto_properTimePhase_quadratic {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    Tendsto (fun τ => (properTimePhase b E r τ - bridgeAction b E r) /
      (τ - bridgeTime b E r) ^ 2) (𝓝[≠] (bridgeTime b E r))
      (𝓝 (properTimeHessian b E r / 2)) := by
  let a := bridgeTime b E r
  have ha : 0 < a := bridgeTime_pos hb hE hr
  have hd0 : deriv (properTimePhase b E r) a = 0 :=
    (hasDerivAt_properTimePhase_bridgeTime hb hE hr).deriv
  have hdd : HasDerivAt (deriv (properTimePhase b E r)) (properTimeHessian b E r) a :=
    (hasDerivAt_deriv_properTimePhase hb ha E r).differentiableAt.hasDerivAt
  have hslope := hdd.tendsto_slope.div_const 2
  simp only [slope_def_field, hd0, sub_zero] at hslope
  have hdiv : Tendsto (fun τ => deriv (properTimePhase b E r) τ / (2 * (τ - a)))
      (𝓝[≠] a) (𝓝 (properTimeHessian b E r / 2)) := by
    convert hslope using 1
    ext τ
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := deriv (properTimePhase b E r)) (g' := fun τ => 2 * (τ - a))
      (a := a) _ _ _ _ _ hdiv
  · filter_upwards [(lt_mem_nhds ha).filter_mono nhdsWithin_le_nhds] with τ hτ
    exact ((hasDerivAt_properTimePhase hb hτ E r).differentiableAt.hasDerivAt.sub_const _)
  · exact Filter.Eventually.of_forall fun τ => by
      convert ((hasDerivAt_id τ).sub_const a).pow 2 using 1
      simp
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hτ)
  · have hcont : ContinuousAt (fun τ => properTimePhase b E r τ - bridgeAction b E r) a :=
      (hasDerivAt_properTimePhase_bridgeTime hb hE hr).continuousAt.sub continuousAt_const
    have hc := hcont.tendsto.mono_left (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)
    simpa only [a, properTimePhase_bridgeTime hb hE hr, sub_self] using hc
  · have hc : ContinuousAt (fun τ : ℝ => (τ - a) ^ 2) a := by fun_prop
    simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      hc.tendsto.mono_left (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)

theorem tendsto_scaled_properTimePhase {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (u : ℝ) :
    Tendsto (fun h : ℝ =>
      (properTimePhase b E r (bridgeTime b E r + Real.sqrt h * u) - bridgeAction b E r) / h)
      (𝓝[>] 0) (𝓝 (properTimeHessian b E r / 2 * u ^ 2)) := by
  by_cases hu : u = 0
  · subst u
    simpa only [mul_zero, add_zero, properTimePhase_bridgeTime hb hE hr, sub_self,
      zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  have hroot : Tendsto (fun h : ℝ => Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have harg : Tendsto (fun h : ℝ => bridgeTime b E r + Real.sqrt h * u)
      (𝓝[>] 0) (𝓝[≠] (bridgeTime b E r)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa only [zero_mul, add_zero] using hroot.mul_const u |>.const_add (bridgeTime b E r)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hhpos : 0 < h := hh
      simp only [mem_compl_iff, mem_singleton_iff, add_eq_left]
      exact mul_ne_zero (Real.sqrt_pos.2 hhpos).ne' hu
  have hlim := ((tendsto_properTimePhase_quadratic hb hE hr).comp harg).mul_const (u ^ 2)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  dsimp only [Function.comp_apply]
  rw [add_sub_cancel_left, mul_pow, Real.sq_sqrt hhpos.le]
  field_simp

def landauLocalProfile (b E r ε h u : ℝ) : ℝ :=
  (Ioo (bridgeTime b E r - ε) (bridgeTime b E r + ε)).indicator
    (fun τ => (Real.sinh (b * τ))⁻¹ *
      Real.exp (-(properTimePhase b E r τ - bridgeAction b E r) / h))
    (bridgeTime b E r + Real.sqrt h * u)

theorem measurable_landauLocalProfile (b E r ε h : ℝ) :
    Measurable (landauLocalProfile b E r ε h) := by
  have hf : Measurable (fun τ : ℝ => (Real.sinh (b * τ))⁻¹ *
      Real.exp (-(properTimePhase b E r τ - bridgeAction b E r) / h)) := by
    unfold properTimePhase
    fun_prop
  exact (hf.indicator measurableSet_Ioo).comp (by fun_prop)

theorem tendsto_landauLocalProfile {b E r ε : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hε : 0 < ε) (u : ℝ) :
    Tendsto (fun h => landauLocalProfile b E r ε h u) (𝓝[>] 0)
      (𝓝 ((Real.sinh (b * bridgeTime b E r))⁻¹ *
        Real.exp (-(properTimeHessian b E r / 2) * u ^ 2))) := by
  have hroot : Tendsto (fun h : ℝ => Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have harg : Tendsto (fun h : ℝ => bridgeTime b E r + Real.sqrt h * u)
      (𝓝[>] 0) (𝓝 (bridgeTime b E r)) := by
    simpa only [zero_mul, add_zero] using hroot.mul_const u |>.const_add (bridgeTime b E r)
  have hs : Real.sinh (b * bridgeTime b E r) ≠ 0 :=
    (Real.sinh_pos_iff.2 (mul_pos hb (bridgeTime_pos hb hE hr))).ne'
  have hamp := ((Real.continuous_sinh.tendsto _).comp (harg.const_mul b)).inv₀ hs
  have hexp := (Real.continuous_exp.tendsto _).comp
    (tendsto_scaled_properTimePhase hb hE hr u).neg
  have hlim := hamp.mul hexp
  have hevent : ∀ᶠ h : ℝ in 𝓝[>] 0,
      bridgeTime b E r + Real.sqrt h * u ∈ Ioo (bridgeTime b E r - ε) (bridgeTime b E r + ε) :=
    harg.eventually (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
  have hlim' : Tendsto (fun h : ℝ =>
      (Real.sinh (b * (bridgeTime b E r + Real.sqrt h * u)))⁻¹ *
        Real.exp (-(properTimePhase b E r (bridgeTime b E r + Real.sqrt h * u) -
          bridgeAction b E r) / h)) (𝓝[>] 0)
      (𝓝 ((Real.sinh (b * bridgeTime b E r))⁻¹ *
        Real.exp (-(properTimeHessian b E r / 2) * u ^ 2))) := by
    simpa only [neg_div, neg_mul, Function.comp_def] using hlim
  apply hlim'.congr'
  filter_upwards [hevent] with h hh
  simp only [landauLocalProfile, indicator_of_mem hh, neg_div]

theorem norm_landauLocalProfile_le {b E r ε h : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hε : 0 < ε)
    (hεa : ε < bridgeTime b E r) (hh : 0 < h) (u : ℝ) :
    ‖landauLocalProfile b E r ε h u‖ ≤
      (Real.sinh (b * (bridgeTime b E r - ε)))⁻¹ *
        Real.exp (-(properTimeHessianFloor b r (bridgeTime b E r + ε) / 2) * u ^ 2) := by
  let a := bridgeTime b E r
  let τ := a + Real.sqrt h * u
  let m := properTimeHessianFloor b r (a + ε)
  have ha : 0 < a := bridgeTime_pos hb hE hr
  have hlo : 0 < a - ε := sub_pos.mpr hεa
  have hslo : 0 < Real.sinh (b * (a - ε)) := Real.sinh_pos_iff.2 (mul_pos hb hlo)
  by_cases hmem : τ ∈ Ioo (a - ε) (a + ε)
  · have hτ : 0 < τ := hlo.trans hmem.1
    have hst : 0 < Real.sinh (b * τ) := Real.sinh_pos_iff.2 (mul_pos hb hτ)
    have hquad := properTimePhase_ge_quadratic hb hE hr
      (show bridgeTime b E r < a + ε by dsimp [a]; linarith)
      (fun t ht => properTimeHessianFloor_le hb hr le_rfl ht.1 ht.2 E) hτ hmem.2.le
    have hsq : (τ - a) ^ 2 = h * u ^ 2 := by
      dsimp [τ]
      rw [add_sub_cancel_left, mul_pow, Real.sq_sqrt hh.le]
    have hq : m / 2 * u ^ 2 ≤ (properTimePhase b E r τ - bridgeAction b E r) / h := by
      apply (le_div_iff₀ hh).2
      change bridgeAction b E r + m / 2 * (τ - a) ^ 2 ≤ _ at hquad
      rw [hsq] at hquad
      nlinarith
    change ‖(Ioo (a - ε) (a + ε)).indicator _ τ‖ ≤ _
    rw [indicator_of_mem hmem, Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.2 hst) (Real.exp_pos _))]
    apply mul_le_mul
    · exact inv_anti₀ hslo (Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_left hmem.1.le hb.le))
    · apply Real.exp_le_exp.mpr
      simpa only [neg_div, neg_mul] using neg_le_neg hq
    · exact (Real.exp_pos _).le
    · exact (inv_pos.2 hslo).le
  · change ‖(Ioo (a - ε) (a + ε)).indicator _ τ‖ ≤ _
    rw [indicator_of_notMem hmem, norm_zero]
    exact mul_nonneg (inv_pos.2 hslo).le (Real.exp_pos _).le

/-- The localized integral has the predicted Gaussian leading term. -/
theorem tendsto_integral_landauLocalProfile {b E r ε : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hε : 0 < ε)
    (hεa : ε < bridgeTime b E r) :
    Tendsto (fun h => ∫ u : ℝ, landauLocalProfile b E r ε h u) (𝓝[>] 0)
      (𝓝 ((Real.sinh (b * bridgeTime b E r))⁻¹ *
        Real.sqrt (2 * Real.pi / properTimeHessian b E r))) := by
  let a := bridgeTime b E r
  let m := properTimeHessianFloor b r (a + ε)
  have hm : 0 < m := properTimeHessianFloor_pos hb hr (by
    dsimp [a]
    linarith [bridgeTime_pos hb hE hr])
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume)
    (fun u : ℝ => (Real.sinh (b * (a - ε)))⁻¹ * Real.exp (-(m / 2) * u ^ 2))
    (Filter.Eventually.of_forall fun h => (measurable_landauLocalProfile b E r ε h).aestronglyMeasurable)
    (show ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ᵐ u : ℝ, ‖landauLocalProfile b E r ε h u‖ ≤
      (Real.sinh (b * (a - ε)))⁻¹ * Real.exp (-(m / 2) * u ^ 2) from by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact Filter.Eventually.of_forall (norm_landauLocalProfile_le hb hE hr hε hεa hh))
    ((integrable_exp_neg_mul_sq (half_pos hm)).const_mul _)
    (Filter.Eventually.of_forall (tendsto_landauLocalProfile hb hE hr hε))
  convert hlim using 1
  rw [integral_const_mul, integral_gaussian]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring_nf

theorem integral_landauLocalProfile_eq {b E r ε h : ℝ} (hh : 0 < h) :
    (∫ u : ℝ, landauLocalProfile b E r ε h u) =
      (Real.sqrt h)⁻¹ * Real.exp (bridgeAction b E r / h) *
        ∫ τ in Ioo (bridgeTime b E r - ε) (bridgeTime b E r + ε), landauIntegrand b h E r τ := by
  let a := bridgeTime b E r
  let g : ℝ → ℝ := (Ioo (a - ε) (a + ε)).indicator
    (fun τ => (Real.sinh (b * τ))⁻¹ * Real.exp (-(properTimePhase b E r τ - bridgeAction b E r) / h))
  change (∫ u : ℝ, g (a + Real.sqrt h * u)) = _
  rw [Measure.integral_comp_mul_left (fun x => g (a + x)), integral_add_left_eq_self]
  rw [abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hh)), smul_eq_mul]
  dsimp only [g]
  rw [integral_indicator measurableSet_Ioo]
  have heq : (fun τ => (Real.sinh (b * τ))⁻¹ *
      Real.exp (-(properTimePhase b E r τ - bridgeAction b E r) / h)) =
      fun τ => Real.exp (bridgeAction b E r / h) * landauIntegrand b h E r τ := by
    funext τ
    unfold landauIntegrand
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul]
  ring

theorem normalized_landauKernel_decomposition {b E r ε h : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r)
    (hεa : ε < bridgeTime b E r) (hh : 0 < h) :
    (h * Real.sqrt h) * Real.exp (bridgeAction b E r / h) * landauKernel b h E r =
      b / (4 * Real.pi) * (∫ u : ℝ, landauLocalProfile b E r ε h u) +
        (h * Real.sqrt h) * Real.exp (bridgeAction b E r / h) * landauTailKernel b h E r ε := by
  let a := bridgeTime b E r
  have hsets : landauTailSet b E r ε = Ioi 0 \ Ioo (a - ε) (a + ε) := by
    ext τ
    simp only [landauTailSet, mem_setOf_eq, mem_diff, mem_Ioi, mem_Ioo, not_and_or,
      not_lt, le_abs]
    constructor
    · rintro ⟨hτ, hleft | hright⟩
      · exact ⟨hτ, Or.inr (by dsimp [a]; linarith)⟩
      · exact ⟨hτ, Or.inl (by dsimp [a]; linarith)⟩
    · rintro ⟨hτ, hleft | hright⟩
      · exact ⟨hτ, Or.inr (by dsimp [a] at hleft; linarith)⟩
      · exact ⟨hτ, Or.inl (by dsimp [a] at hright; linarith)⟩
  have hsub : Ioo (a - ε) (a + ε) ⊆ Ioi 0 :=
    fun τ hτ => (sub_pos.mpr hεa).trans hτ.1
  have hsplit : (∫ τ in Ioi (0 : ℝ), landauIntegrand b h E r τ) =
      (∫ τ in Ioo (a - ε) (a + ε), landauIntegrand b h E r τ) +
        ∫ τ in landauTailSet b E r ε, landauIntegrand b h E r τ := by
    rw [hsets, setIntegral_diff measurableSet_Ioo (integrableOn_landauIntegrand hb hh hE hr) hsub]
    ring
  rw [integral_landauLocalProfile_eq hh]
  unfold landauKernel landauTailKernel
  rw [hsplit]
  have hs : (Real.sqrt h) ^ 2 = h := Real.sq_sqrt hh.le
  have hsn : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * (∫ τ in Ioo (a - ε) (a + ε), landauIntegrand b h E r τ)) hs]

def landauLeadingCoefficient (b E r : ℝ) : ℝ :=
  b / (4 * Real.pi) * (Real.sinh (b * bridgeTime b E r))⁻¹ *
    Real.sqrt (2 * Real.pi / properTimeHessian b E r)

theorem landauLeadingCoefficient_pos {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) : 0 < landauLeadingCoefficient b E r := by
  unfold landauLeadingCoefficient
  have hs : 0 < Real.sinh (b * bridgeTime b E r) :=
    Real.sinh_pos_iff.2 (mul_pos hb (bridgeTime_pos hb hE hr))
  have hD := properTimeHessian_pos hb hE hr
  positivity

/-- The actual leading Laplace asymptotic, with the factor written as `h * sqrt h`. -/
theorem tendsto_normalized_landauKernel {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    Tendsto (fun h : ℝ => (h * Real.sqrt h) * Real.exp (bridgeAction b E r / h) *
      landauKernel b h E r) (𝓝[>] 0) (𝓝 (landauLeadingCoefficient b E r)) := by
  let ε := bridgeTime b E r / 2
  have hε : 0 < ε := half_pos (bridgeTime_pos hb hE hr)
  have hεa : ε < bridgeTime b E r := by dsimp [ε]; linarith [bridgeTime_pos hb hE hr]
  have hlocal := (tendsto_integral_landauLocalProfile hb hE hr hε hεa).const_mul (b / (4 * Real.pi))
  have htail : Tendsto (fun h : ℝ => Real.exp (bridgeAction b E r / h) * landauTailKernel b h E r ε)
      (𝓝[>] 0) (𝓝 0) := by
    have ht := (tendstoUniformlyOn_normalized_landauTailKernel hb hE le_rfl hr le_rfl hε 0).tendsto_at
      (x := (E, r)) (show (E, r) ∈ Icc E E ×ˢ Icc r r from ⟨⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩⟩)
    simpa only [pow_zero, inv_one, one_mul] using ht
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hroot : Tendsto (fun h : ℝ => Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.tendsto 0 |>.comp hid
  have hall := hlocal.add ((hid.mul hroot).mul htail)
  have hall' : Tendsto (fun h : ℝ =>
      b / (4 * Real.pi) * (∫ u : ℝ, landauLocalProfile b E r ε h u) +
        (h * Real.sqrt h) * Real.exp (bridgeAction b E r / h) * landauTailKernel b h E r ε)
      (𝓝[>] 0) (𝓝 (landauLeadingCoefficient b E r)) := by
    simpa only [zero_mul, mul_zero, add_zero, mul_assoc, landauLeadingCoefficient] using hall
  apply hall'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (normalized_landauKernel_decomposition hb hE hr hεa hh).symm

/-- The leading coefficient and semiclassical power of the blueprint's Laplace formula. -/
theorem tendsto_h_three_halves_exp_mul_landauKernel {b E r : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) :
    Tendsto (fun h : ℝ => h ^ (3 / 2 : ℝ) * Real.exp (bridgeAction b E r / h) *
      landauKernel b h E r) (𝓝[>] 0) (𝓝 (landauLeadingCoefficient b E r)) := by
  apply (tendsto_normalized_landauKernel hb hE hr).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hhpos, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

end InfiniteZero
