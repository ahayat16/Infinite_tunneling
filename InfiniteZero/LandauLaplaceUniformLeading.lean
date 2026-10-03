import InfiniteZero.LandauLaplaceLeading
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The Landau leading coefficient for moving positive parameters

Taylor's theorem at the moving minimum, a common Gaussian majorant and
uniform tail estimates extend the scalar Laplace limit to varying energy
and radius. No parameter-dependent asymptotic is supplied as a hypothesis.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace InfiniteZero

theorem contDiffOn_properTimePhase {b : ℝ} (hb : 0 < b) (E r : ℝ) (n : ℕ∞) :
    ContDiffOn ℝ n (properTimePhase b E r) (Ioi 0) := by
  have hlin : ContDiff ℝ n (fun t : ℝ => b * t) := by fun_prop
  have hs : ∀ t ∈ Ioi (0 : ℝ), Real.sinh (b * t) ≠ 0 := fun t ht =>
    (Real.sinh_pos_iff.mpr (mul_pos hb ht)).ne'
  exact ((contDiff_const.mul contDiff_id).contDiffOn).add
    (contDiffOn_const.mul (hlin.cosh.contDiffOn.div hlin.sinh.contDiffOn hs))

/-- A genuine second-order mean-value formula around the exact minimum. -/
theorem exists_properTimePhase_quadratic_point {b E r τ : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hr : 0 < r) (hτ : 0 < τ) :
    ∃ ξ ∈ uIcc (bridgeTime b E r) τ,
      properTimePhase b E r τ - bridgeAction b E r =
        deriv (deriv (properTimePhase b E r)) ξ / 2 * (τ - bridgeTime b E r) ^ 2 := by
  let a := bridgeTime b E r
  have ha : 0 < a := bridgeTime_pos hb hE hr
  by_cases heq : a = τ
  · refine ⟨a, ?_, ?_⟩
    · simp [heq]
    · rw [← heq]
      simp [a, properTimePhase_bridgeTime hb hE hr]
  have hminmax : min a τ < max a τ := by
    rcases lt_or_gt_of_ne heq with h | h <;> simp [h.le, h]
  have hsub : uIcc a τ ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact (lt_min ha hτ).trans_le ht.1
  have hu := uniqueDiffOn_Icc hminmax
  have hderiv : derivWithin (properTimePhase b E r) (uIcc a τ) a = 0 :=
    (hasDerivAt_properTimePhase_bridgeTime hb hE hr).hasDerivWithinAt.derivWithin
      (hu a (left_mem_uIcc))
  obtain ⟨ξ, hξ, htaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) heq ((contDiffOn_properTimePhase hb E r 2).mono hsub)
  refine ⟨ξ, Ioo_subset_Icc_self hξ, ?_⟩
  have htaylor' : properTimePhase b E r τ - properTimePhase b E r a =
      deriv (deriv (properTimePhase b E r)) ξ * (τ - a) ^ 2 / 2 := by
    simpa [taylorWithinEval_succ, iteratedDerivWithin_one, hderiv,
      iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial] using htaylor
  rw [properTimePhase_bridgeTime hb hE hr] at htaylor'
  simpa only [div_mul_eq_mul_div] using htaylor'

theorem tendsto_bridgeTime_parameters {ι : Type*} {l : Filter ι} {E r : ι → ℝ}
    {E₀ r₀ : ℝ} (b : ℝ) (hE₀ : 0 < E₀)
    (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i => bridgeTime b (E i) (r i)) l (𝓝 (bridgeTime b E₀ r₀)) := by
  unfold bridgeTime
  exact ((Real.continuous_arsinh.tendsto _).comp
    ((hr.const_mul b).div (((Real.continuous_sqrt.tendsto E₀).comp hE).const_mul 2)
      (by positivity))).div_const b

/-- The local quadratic limit remains valid when both parameters move. -/
theorem tendsto_scaled_properTimePhase_parameters
    {ι : Type*} {l : Filter ι} {h E r : ι → ℝ} {b E₀ r₀ : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀)) (u : ℝ) :
    Tendsto (fun i =>
      (properTimePhase b (E i) (r i)
        (bridgeTime b (E i) (r i) + Real.sqrt (h i) * u) - bridgeAction b (E i) (r i)) / h i)
      l (𝓝 (properTimeHessian b E₀ r₀ / 2 * u ^ 2)) := by
  classical
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
  have hpos : ∀ᶠ i in l, 0 < E i ∧ 0 < r i ∧ 0 < τ i :=
    (hE.eventually (lt_mem_nhds hE₀)).and
      ((hr.eventually (lt_mem_nhds hr₀)).and (hτ.eventually (lt_mem_nhds ha₀)))
  have hchoose : ∀ i, ∃ ξ : ℝ, (0 < E i ∧ 0 < r i ∧ 0 < τ i) →
      ξ ∈ uIcc (a i) (τ i) ∧
      properTimePhase b (E i) (r i) (τ i) - bridgeAction b (E i) (r i) =
        deriv (deriv (properTimePhase b (E i) (r i))) ξ / 2 * (τ i - a i) ^ 2 := by
    intro i
    by_cases hi : 0 < E i ∧ 0 < r i ∧ 0 < τ i
    · obtain ⟨ξ, hmem, hform⟩ := exists_properTimePhase_quadratic_point hb hi.1 hi.2.1 hi.2.2
      exact ⟨ξ, fun _ => ⟨hmem, hform⟩⟩
    · exact ⟨a₀, fun h => (hi h).elim⟩
  choose ξ hξ using hchoose
  have hspec : ∀ᶠ i in l, ξ i ∈ uIcc (a i) (τ i) ∧
      properTimePhase b (E i) (r i) (τ i) - bridgeAction b (E i) (r i) =
        deriv (deriv (properTimePhase b (E i) (r i))) (ξ i) / 2 * (τ i - a i) ^ 2 :=
    hpos.mono fun i hi => hξ i hi
  have hξlim : Tendsto ξ l (𝓝 a₀) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun i => min (a i) (τ i)) l (𝓝 a₀) by simpa using ha.min hτ)
      (show Tendsto (fun i => max (a i) (τ i)) l (𝓝 a₀) by simpa using ha.max hτ)
      (hspec.mono fun i hi => hi.1.1) (hspec.mono fun i hi => hi.1.2)
  have hs : Real.sinh (b * a₀) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hb ha₀)).ne'
  have hD := (((hr.pow 2).const_mul (b ^ 3)).mul
      ((Real.continuous_cosh.tendsto _).comp (hξlim.const_mul b))).div
    ((((Real.continuous_sinh.tendsto _).comp (hξlim.const_mul b)).pow 3).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hs))
  have hD' : Tendsto (fun i => deriv (deriv (properTimePhase b (E i) (r i))) (ξ i))
      l (𝓝 (properTimeHessian b E₀ r₀)) := by
    have hD₀ : properTimeHessian b E₀ r₀ =
        b ^ 3 * r₀ ^ 2 * Real.cosh (b * a₀) / (2 * Real.sinh (b * a₀) ^ 3) :=
      deriv2_properTimePhase hb ha₀ E₀ r₀
    rw [hD₀]
    apply hD.congr'
    filter_upwards [hξlim.eventually (lt_mem_nhds ha₀)] with i hi
    exact (deriv2_properTimePhase hb hi (E i) (r i)).symm
  apply ((hD'.div_const 2).mul_const (u ^ 2)).congr'
  filter_upwards [hspec, hh.eventually self_mem_nhdsWithin] with i hi hhi
  have hhip : 0 < h i := hhi
  change _ = (properTimePhase b (E i) (r i) (τ i) - bridgeAction b (E i) (r i)) / h i
  rw [hi.2]
  dsimp only [τ]
  rw [add_sub_cancel_left, mul_pow, Real.sq_sqrt hhip.le]
  field_simp

theorem tendsto_landauLocalProfile_parameters
    {ι : Type*} {l : Filter ι} {h E r : ι → ℝ} {b E₀ r₀ ε : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀) (hε : 0 < ε)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀)) (u : ℝ) :
    Tendsto (fun i => landauLocalProfile b (E i) (r i) ε (h i) u) l
      (𝓝 ((Real.sinh (b * bridgeTime b E₀ r₀))⁻¹ *
        Real.exp (-(properTimeHessian b E₀ r₀ / 2) * u ^ 2))) := by
  have hroot : Tendsto (fun i => Real.sqrt (h i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (hh.mono_right nhdsWithin_le_nhds)
  have hshift : Tendsto (fun i => Real.sqrt (h i) * u) l (𝓝 0) := by
    simpa only [zero_mul] using hroot.mul_const u
  have harg : Tendsto (fun i => bridgeTime b (E i) (r i) + Real.sqrt (h i) * u)
      l (𝓝 (bridgeTime b E₀ r₀)) := by
    simpa only [add_zero] using (tendsto_bridgeTime_parameters b hE₀ hE hr).add hshift
  have hs : Real.sinh (b * bridgeTime b E₀ r₀) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hb (bridgeTime_pos hb hE₀ hr₀))).ne'
  have hamp := ((Real.continuous_sinh.tendsto _).comp (harg.const_mul b)).inv₀ hs
  have hexp := (Real.continuous_exp.tendsto _).comp
    (tendsto_scaled_properTimePhase_parameters hb hE₀ hr₀ hh hE hr u).neg
  have hlim := hamp.mul hexp
  simp only [Function.comp_def] at hlim
  have hwindow : ∀ᶠ i in l, Real.sqrt (h i) * u ∈ Ioo (-ε) ε :=
    hshift.eventually (isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos hε, hε⟩)
  simp only [neg_mul]
  apply hlim.congr'
  filter_upwards [hwindow] with i hi
  have hmem : bridgeTime b (E i) (r i) + Real.sqrt (h i) * u ∈
      Ioo (bridgeTime b (E i) (r i) - ε) (bridgeTime b (E i) (r i) + ε) := by
    constructor <;> linarith [hi.1, hi.2]
  simp only [landauLocalProfile, indicator_of_mem hmem, neg_div]

/-- A common Gaussian bound for the local profiles on a positive rectangle. -/
theorem norm_landauLocalProfile_uniform_le {b Emin Emax rmin rmax E r ε h : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hrmin : 0 < rmin)
    (hE : E ∈ Icc Emin Emax) (hr : r ∈ Icc rmin rmax)
    (hε : 0 < ε) (hεa : ε < bridgeTime b Emax rmin) (hh : 0 < h) (u : ℝ) :
    ‖landauLocalProfile b E r ε h u‖ ≤
      (Real.sinh (b * (bridgeTime b Emax rmin - ε)))⁻¹ *
        Real.exp (-(properTimeHessianFloor b rmin (bridgeTime b Emin rmax + ε) / 2) * u ^ 2) := by
  have hEp : 0 < E := hEmin.trans_le hE.1
  have hrp : 0 < r := hrmin.trans_le hr.1
  have ha := bridgeTime_pos hb hEp hrp
  have hbox := bridgeTime_mem_uniform_Icc hb hEmin hrmin hE hr
  have hlocal := norm_landauLocalProfile_le hb hEp hrp hε (hεa.trans_le hbox.1) hh u
  have hm : properTimeHessianFloor b rmin (bridgeTime b Emin rmax + ε) ≤
      properTimeHessianFloor b r (bridgeTime b E r + ε) := by
    unfold properTimeHessianFloor
    have hs : 0 < Real.sinh (b * (bridgeTime b E r + ε)) :=
      Real.sinh_pos_iff.mpr (mul_pos hb (add_pos ha hε))
    refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · gcongr
      exact hr.1
    · gcongr
      exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left
        (show bridgeTime b E r + ε ≤ bridgeTime b Emin rmax + ε by linarith [hbox.2]) hb.le)
  apply hlocal.trans
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le ?_
  · apply inv_anti₀
    · exact Real.sinh_pos_iff.mpr (mul_pos hb (sub_pos.mpr hεa))
    · exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left
        (sub_le_sub_right hbox.1 ε) hb.le)
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg u)]
  · exact (inv_pos.mpr (Real.sinh_pos_iff.mpr (mul_pos hb (sub_pos.mpr hεa)))).le

theorem tendsto_integral_landauLocalProfile_parameters
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {b E₀ r₀ Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hEmin : 0 < Emin) (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax)
    (hε : 0 < ε) (hεa : ε < bridgeTime b Emax rmin)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀))
    (hEbox : ∀ᶠ i in l, E i ∈ Icc Emin Emax) (hrbox : ∀ᶠ i in l, r i ∈ Icc rmin rmax) :
    Tendsto (fun i => ∫ u : ℝ, landauLocalProfile b (E i) (r i) ε (h i) u) l
      (𝓝 ((Real.sinh (b * bridgeTime b E₀ r₀))⁻¹ *
        Real.sqrt (2 * Real.pi / properTimeHessian b E₀ r₀))) := by
  let m := properTimeHessianFloor b rmin (bridgeTime b Emin rmax + ε)
  let B := (Real.sinh (b * (bridgeTime b Emax rmin - ε)))⁻¹
  have hm : 0 < m := properTimeHessianFloor_pos hb hrmin
    (add_pos (bridgeTime_pos hb hEmin (hrmin.trans_le hrmax)) hε)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (fun u : ℝ => B * Real.exp (-(m / 2) * u ^ 2))
    (Eventually.of_forall fun i =>
      (measurable_landauLocalProfile b (E i) (r i) ε (h i)).aestronglyMeasurable)
    (show ∀ᶠ i in l, ∀ᵐ u : ℝ, ‖landauLocalProfile b (E i) (r i) ε (h i) u‖ ≤
        B * Real.exp (-(m / 2) * u ^ 2) from by
      filter_upwards [hEbox, hrbox, hh.eventually self_mem_nhdsWithin] with i hiE hir hih
      exact Eventually.of_forall (norm_landauLocalProfile_uniform_le hb hEmin hrmin hiE hir hε hεa hih))
    ((integrable_exp_neg_mul_sq (half_pos hm)).const_mul B)
    (Eventually.of_forall (tendsto_landauLocalProfile_parameters hb hE₀ hr₀ hε hh hE hr))
  convert hlim using 1
  rw [integral_const_mul, integral_gaussian]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring_nf

/-- The true leading coefficient along arbitrary convergent positive parameters. -/
theorem tendsto_normalized_landauKernel_parameters
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {b E₀ r₀ : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i => (h i * Real.sqrt (h i)) * Real.exp (bridgeAction b (E i) (r i) / h i) *
      landauKernel b (h i) (E i) (r i)) l (𝓝 (landauLeadingCoefficient b E₀ r₀)) := by
  let ε := bridgeTime b (2 * E₀) (r₀ / 2) / 2
  have hamin : 0 < bridgeTime b (2 * E₀) (r₀ / 2) :=
    bridgeTime_pos hb (by positivity) (half_pos hr₀)
  have hε : 0 < ε := half_pos hamin
  have hεa : ε < bridgeTime b (2 * E₀) (r₀ / 2) := by dsimp [ε]; linarith
  have hEbox : ∀ᶠ i in l, E i ∈ Icc (E₀ / 2) (2 * E₀) :=
    hE.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hrbox : ∀ᶠ i in l, r i ∈ Icc (r₀ / 2) (2 * r₀) :=
    hr.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hlocal := (tendsto_integral_landauLocalProfile_parameters hb hE₀ hr₀
    (half_pos hE₀) (half_pos hr₀) (show r₀ / 2 ≤ 2 * r₀ by linarith)
    hε hεa hh hE hr hEbox hrbox).const_mul (b / (4 * Real.pi))
  obtain ⟨C, hC, d, hd, hbound⟩ := exists_uniform_landauTailKernel_bound hb
    (half_pos hE₀) (show E₀ / 2 ≤ 2 * E₀ by linarith)
    (half_pos hr₀) (show r₀ / 2 ≤ 2 * r₀ by linarith) hε
  have htail : Tendsto (fun i => Real.exp (bridgeAction b (E i) (r i) / h i) *
      landauTailKernel b (h i) (E i) (r i) ε) l (𝓝 0) := by
    have ht : Tendsto (fun i => C * Real.exp (-d / h i)) l (𝓝 0) := by
      simpa only [pow_zero, inv_one, one_mul, mul_zero, Function.comp_def] using
        ((tendsto_inv_pow_mul_exp_neg_div hd 0).comp hh).const_mul C
    apply squeeze_zero' _ _ ht
    · filter_upwards [hh.eventually self_mem_nhdsWithin] with i hi
      exact mul_nonneg (Real.exp_pos _).le (landauTailKernel_nonneg hb hi _ _ _)
    · filter_upwards [hEbox, hrbox, hh.eventually self_mem_nhdsWithin] with i hiE hir hih
      exact hbound (E i) hiE (r i) hir (h i) hih
  have hzero := hh.mono_right nhdsWithin_le_nhds
  have hroot : Tendsto (fun i => Real.sqrt (h i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hzero
  have hall := hlocal.add ((hzero.mul hroot).mul htail)
  have hall' : Tendsto (fun i =>
      b / (4 * Real.pi) * (∫ u : ℝ, landauLocalProfile b (E i) (r i) ε (h i) u) +
        (h i * Real.sqrt (h i)) * Real.exp (bridgeAction b (E i) (r i) / h i) *
          landauTailKernel b (h i) (E i) (r i) ε)
      l (𝓝 (landauLeadingCoefficient b E₀ r₀)) := by
    simpa only [zero_mul, mul_zero, add_zero, mul_assoc, landauLeadingCoefficient] using hall
  apply hall'.congr'
  filter_upwards [hEbox, hrbox, hh.eventually self_mem_nhdsWithin] with i hiE hir hih
  have hEp : 0 < E i := (half_pos hE₀).trans_le hiE.1
  have hrp : 0 < r i := (half_pos hr₀).trans_le hir.1
  have hea : ε < bridgeTime b (E i) (r i) := hεa.trans_le
    (bridgeTime_mem_uniform_Icc hb (half_pos hE₀) (half_pos hr₀) hiE hir).1
  exact (normalized_landauKernel_decomposition hb hEp hrp hea hih).symm

theorem tendsto_h_three_halves_exp_mul_landauKernel_parameters
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {b E₀ r₀ : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i => (h i) ^ (3 / 2 : ℝ) * Real.exp (bridgeAction b (E i) (r i) / h i) *
      landauKernel b (h i) (E i) (r i)) l (𝓝 (landauLeadingCoefficient b E₀ r₀)) := by
  apply (tendsto_normalized_landauKernel_parameters hb hE₀ hr₀ hh hE hr).congr'
  filter_upwards [hh.eventually self_mem_nhdsWithin] with i hi
  have hip : 0 < h i := hi
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hip,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem tendsto_properTimeHessian_parameters
    {ι : Type*} {l : Filter ι} {E r : ι → ℝ} {b E₀ r₀ : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i => properTimeHessian b (E i) (r i)) l
      (𝓝 (properTimeHessian b E₀ r₀)) := by
  have ha := tendsto_bridgeTime_parameters b hE₀ hE hr
  have ha₀ := bridgeTime_pos hb hE₀ hr₀
  have hs : Real.sinh (b * bridgeTime b E₀ r₀) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hb ha₀)).ne'
  have hD := (((hr.pow 2).const_mul (b ^ 3)).mul
      ((Real.continuous_cosh.tendsto _).comp (ha.const_mul b))).div
    ((((Real.continuous_sinh.tendsto _).comp (ha.const_mul b)).pow 3).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hs))
  have hD₀ : properTimeHessian b E₀ r₀ =
      b ^ 3 * r₀ ^ 2 * Real.cosh (b * bridgeTime b E₀ r₀) /
        (2 * Real.sinh (b * bridgeTime b E₀ r₀) ^ 3) :=
    deriv2_properTimePhase hb ha₀ E₀ r₀
  rw [hD₀]
  apply hD.congr'
  filter_upwards [ha.eventually (lt_mem_nhds ha₀)] with i hi
  exact (deriv2_properTimePhase hb hi (E i) (r i)).symm

theorem tendsto_landauLeadingCoefficient_parameters
    {ι : Type*} {l : Filter ι} {E r : ι → ℝ} {b E₀ r₀ : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i => landauLeadingCoefficient b (E i) (r i)) l
      (𝓝 (landauLeadingCoefficient b E₀ r₀)) := by
  have ha := tendsto_bridgeTime_parameters b hE₀ hE hr
  have hs : Real.sinh (b * bridgeTime b E₀ r₀) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hb (bridgeTime_pos hb hE₀ hr₀))).ne'
  have hamp := (((Real.continuous_sinh.tendsto _).comp (ha.const_mul b)).inv₀ hs).const_mul
    (b / (4 * Real.pi))
  have hD := tendsto_properTimeHessian_parameters hb hE₀ hr₀ hE hr
  have hroot := (Real.continuous_sqrt.tendsto _).comp
    ((tendsto_const_nhds (x := 2 * Real.pi)).div hD (properTimeHessian_pos hb hE₀ hr₀).ne')
  exact hamp.mul hroot

/-- Joint convergence at each positive parameter gives locally uniform convergence. -/
theorem tendstoLocallyUniformlyOn_landauKernel_leading {b : ℝ} (hb : 0 < b) :
    TendstoLocallyUniformlyOn
      (fun h (p : ℝ × ℝ) => h ^ (3 / 2 : ℝ) * Real.exp (bridgeAction b p.1 p.2 / h) *
        landauKernel b h p.1 p.2)
      (fun p => landauLeadingCoefficient b p.1 p.2) (𝓝[>] 0) (Ioi 0 ×ˢ Ioi 0) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro p hp
  have hpar : Tendsto (fun q : ℝ × (ℝ × ℝ) => q.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝[Ioi 0 ×ˢ Ioi 0] p) (𝓝 p) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hE := (continuous_fst.tendsto p).comp hpar
  have hr := (continuous_snd.tendsto p).comp hpar
  have hk := tendsto_landauLeadingCoefficient_parameters hb hp.1 hp.2 hE hr
  have hmain := tendsto_h_three_halves_exp_mul_landauKernel_parameters hb hp.1 hp.2
    tendsto_fst hE hr
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  simpa only [dist_self] using hk.dist hmain

/-- The actual Landau leading asymptotic is uniform on every positive compact set. -/
theorem tendstoUniformlyOn_landauKernel_leading {b : ℝ} (hb : 0 < b)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0 ×ˢ Ioi 0) :
    TendstoUniformlyOn
      (fun h (p : ℝ × ℝ) => h ^ (3 / 2 : ℝ) * Real.exp (bridgeAction b p.1 p.2 / h) *
        landauKernel b h p.1 p.2)
      (fun p => landauLeadingCoefficient b p.1 p.2) (𝓝[>] 0) K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((tendstoLocallyUniformlyOn_landauKernel_leading hb).mono hKpos)

theorem tendstoUniformlyOn_landauKernel_leading_rectangle
    {b Emin Emax rmin rmax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin) (hrmin : 0 < rmin) :
    TendstoUniformlyOn
      (fun h (p : ℝ × ℝ) => h ^ (3 / 2 : ℝ) * Real.exp (bridgeAction b p.1 p.2 / h) *
        landauKernel b h p.1 p.2)
      (fun p => landauLeadingCoefficient b p.1 p.2) (𝓝[>] 0)
      (Icc Emin Emax ×ˢ Icc rmin rmax) := by
  apply tendstoUniformlyOn_landauKernel_leading hb (isCompact_Icc.prod isCompact_Icc)
  intro p hp
  exact ⟨hEmin.trans_le hp.1.1, hrmin.trans_le hp.2.1⟩

/-- The positive leading coefficient permits the relative `1 + o(1)` form. -/
theorem tendsto_landauKernel_relative_parameters
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {b E₀ r₀ : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀)) (hr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i => ((h i) ^ (3 / 2 : ℝ) * Real.exp (bridgeAction b (E i) (r i) / h i) *
      landauKernel b (h i) (E i) (r i)) / landauLeadingCoefficient b (E i) (r i)) l (𝓝 1) := by
  have hne := (landauLeadingCoefficient_pos hb hE₀ hr₀).ne'
  simpa only [div_self hne] using
    (tendsto_h_three_halves_exp_mul_landauKernel_parameters hb hE₀ hr₀ hh hE hr).div
      (tendsto_landauLeadingCoefficient_parameters hb hE₀ hr₀ hE hr) hne

theorem tendstoUniformlyOn_landauKernel_relative {b : ℝ} (hb : 0 < b)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0 ×ˢ Ioi 0) :
    TendstoUniformlyOn
      (fun h (p : ℝ × ℝ) => (h ^ (3 / 2 : ℝ) * Real.exp (bridgeAction b p.1 p.2 / h) *
        landauKernel b h p.1 p.2) / landauLeadingCoefficient b p.1 p.2)
      (fun _ => 1) (𝓝[>] 0) K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro p hp
  have hp' := hKpos hp
  have hpar : Tendsto (fun q : ℝ × (ℝ × ℝ) => q.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝[K] p) (𝓝 p) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hE := (continuous_fst.tendsto p).comp hpar
  have hr := (continuous_snd.tendsto p).comp hpar
  exact Uniform.tendsto_nhds_right.mp
    (tendsto_landauKernel_relative_parameters hb hp'.1 hp'.2 tendsto_fst hE hr)

end InfiniteZero
