import InfiniteZero.LandauLaplace

/-!
# Exponentially negligible noncritical proper times

This is the order-zero tail estimate in P2.3. The integration domain is the
full positive time axis outside a fixed neighborhood of the critical point.
The estimates are uniform on positive energy-radius rectangles.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def landauTailSet (b E r ε : ℝ) : Set ℝ :=
  {τ | 0 < τ ∧ ε ≤ |τ - bridgeTime b E r|}

def landauTailKernel (b h E r ε : ℝ) : ℝ :=
  b / (4 * Real.pi * h ^ 2) *
    ∫ τ in landauTailSet b E r ε, landauIntegrand b h E r τ

theorem measurableSet_landauTailSet (b E r ε : ℝ) : MeasurableSet (landauTailSet b E r ε) := by
  unfold landauTailSet
  have hm : Measurable (fun τ : ℝ => |τ - bridgeTime b E r|) := by fun_prop
  exact measurableSet_Ioi.inter (measurableSet_le measurable_const hm)

theorem landauTailSet_subset (b E r ε : ℝ) : landauTailSet b E r ε ⊆ Ioi 0 :=
  fun _ h => h.1

theorem integrableOn_landauTailSet {b h E r : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r) (ε : ℝ) :
    IntegrableOn (landauIntegrand b h E r) (landauTailSet b E r ε) :=
  (integrableOn_landauIntegrand hb hh hE hr).mono_set (landauTailSet_subset b E r ε)

theorem landauTailKernel_nonneg {b h : ℝ} (hb : 0 < b) (hh : 0 < h) (E r ε : ℝ) :
    0 ≤ landauTailKernel b h E r ε := by
  unfold landauTailKernel
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_landauTailSet b E r ε)] with τ hτ
  exact (landauIntegrand_pos hb hτ.1 h E r).le

/-- Integrating a phase lower bound over an arbitrary measurable subset of positive times. -/
theorem restricted_landauKernel_le {b h E r α A : ℝ} {s : Set ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : MeasurableSet s) (hspos : s ⊆ Ioi 0)
    (hphase : ∀ τ ∈ s, A ≤ properTimePhase b E r τ) :
    b / (4 * Real.pi * h ^ 2) * (∫ τ in s, landauIntegrand b h E r τ) ≤
      (1 / (Real.pi * E * r ^ 2 * α ^ 2)) * Real.exp (-((1 - α) * A) / h) := by
  have hhα : 0 < h / α := div_pos hh hα
  have hi := integrableOn_landauIntegrand hb hh hE hr
  have hiα := integrableOn_landauIntegrand hb hhα hE hr
  have hpoint (τ : ℝ) (hτ : τ ∈ s) : landauIntegrand b h E r τ ≤
      Real.exp (-((1 - α) * A) / h) * landauIntegrand b (h / α) E r τ := by
    have hfactor : landauIntegrand b h E r τ =
        Real.exp (-((1 - α) * properTimePhase b E r τ) / h) *
          landauIntegrand b (h / α) E r τ := by
      unfold landauIntegrand
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      field_simp
      ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_right _ (landauIntegrand_pos hb (hspos hτ) (h / α) E r).le
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (neg_le_neg (mul_le_mul_of_nonneg_left (hphase τ hτ) (sub_nonneg.mpr hα1))) hh.le
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] landauIntegrand b (h / α) E r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact (landauIntegrand_pos hb hτ (h / α) E r).le
  have hI : (∫ τ in s, landauIntegrand b h E r τ) ≤
      Real.exp (-((1 - α) * A) / h) *
        ∫ τ in Ioi (0 : ℝ), landauIntegrand b (h / α) E r τ := by
    calc
      _ ≤ ∫ τ in s, Real.exp (-((1 - α) * A) / h) * landauIntegrand b (h / α) E r τ :=
        setIntegral_mono_on (hi.mono_set hspos) ((hiα.mono_set hspos).const_mul _) hs hpoint
      _ = Real.exp (-((1 - α) * A) / h) * ∫ τ in s, landauIntegrand b (h / α) E r τ :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hiα hn (Filter.Eventually.of_forall hspos)) (Real.exp_pos _).le
  have hI' := hI.trans (mul_le_mul_of_nonneg_left
    (integral_landauIntegrand_le hb hhα hE hr) (Real.exp_pos _).le)
  have hK := mul_le_mul_of_nonneg_left hI'
    (show 0 ≤ b / (4 * Real.pi * h ^ 2) by positivity)
  convert hK using 1
  field_simp

/-- Uniform exponential suppression after normalization by the minimum action. -/
theorem exists_uniform_landauTailKernel_bound {b Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) (hε : 0 < ε) :
    ∃ C > 0, ∃ d > 0, ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rmin rmax, ∀ h > 0,
      Real.exp (bridgeAction b E r / h) * landauTailKernel b h E r ε ≤
        C * Real.exp (-d / h) := by
  obtain ⟨q, hq, hgap⟩ := exists_uniform_properTimePhase_gap hb hEmin hrmin hrmax hε
  have hEm := hEmin.trans_le hEmax
  have hrm := hrmin.trans_le hrmax
  let Jmax := bridgeAction b Emax rmax
  have hJmax : 0 < Jmax := bridgeAction_pos hb.ne' hEm hrm
  let α := q / (2 * (Jmax + q))
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by
    dsimp [α]
    apply (div_le_one (by positivity : 0 < 2 * (Jmax + q))).2
    linarith
  have hαEq : α * (Jmax + q) = q / 2 := by dsimp [α]; field_simp
  let C := 1 / (Real.pi * Emin * rmin ^ 2 * α ^ 2)
  refine ⟨C, by dsimp [C]; positivity, q / 2, half_pos hq, ?_⟩
  intro E hE r hr h hh
  have hEp := hEmin.trans_le hE.1
  have hrp := hrmin.trans_le hr.1
  have hJ : bridgeAction b E r ≤ Jmax :=
    ((strictMono_bridgeAction hb.ne' hEp).monotone hr.2).trans
      (bridgeAction_energy_le hb.ne' hrm hEp hE.2)
  have hbound := restricted_landauKernel_le hb hh hEp hrp hα hα1
    (measurableSet_landauTailSet b E r ε) (landauTailSet_subset b E r ε)
    (fun τ hτ => hgap E hE r hr τ hτ.1 hτ.2)
  change landauTailKernel b h E r ε ≤ _ at hbound
  have hC : 1 / (Real.pi * E * r ^ 2 * α ^ 2) ≤ C := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    · exact hE.1
    · exact hr.1
  have hcost : bridgeAction b E r - (1 - α) * (bridgeAction b E r + q) ≤ -(q / 2) := by
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hJ (le_rfl : q ≤ q)) hα.le
    rw [hαEq] at hmul
    nlinarith
  calc
    _ ≤ Real.exp (bridgeAction b E r / h) *
        (C * Real.exp (-((1 - α) * (bridgeAction b E r + q)) / h)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact hbound.trans (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)
    _ = C * Real.exp ((bridgeAction b E r - (1 - α) * (bridgeAction b E r + q)) / h) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * Real.exp (-(q / 2) / h) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hcost hh.le)

theorem tendsto_inv_pow_mul_exp_neg_div {d : ℝ} (hd : 0 < d) (N : ℕ) :
    Tendsto (fun h : ℝ => (h ^ N)⁻¹ * Real.exp (-d / h)) (𝓝[>] 0) (𝓝 0) := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) d hd).comp
    (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop)
  simpa only [Function.comp_def, Real.rpow_natCast, inv_pow, div_eq_mul_inv] using hlim

/-- Every fixed negative integer power of `h` is absorbed, uniformly in the parameters. -/
theorem tendstoUniformlyOn_normalized_landauTailKernel {b Emin Emax rmin rmax ε : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hrmin : 0 < rmin) (hrmax : rmin ≤ rmax) (hε : 0 < ε) (N : ℕ) :
    TendstoUniformlyOn
      (fun h (p : ℝ × ℝ) => (h ^ N)⁻¹ * Real.exp (bridgeAction b p.1 p.2 / h) *
        landauTailKernel b h p.1 p.2 ε)
      (fun _ => 0) (𝓝[>] 0) (Icc Emin Emax ×ˢ Icc rmin rmax) := by
  obtain ⟨C, hC, d, hd, hbound⟩ := exists_uniform_landauTailKernel_bound
    hb hEmin hEmax hrmin hrmax hε
  have hlim : Tendsto (fun h : ℝ => C * ((h ^ N)⁻¹ * Real.exp (-d / h)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_inv_pow_mul_exp_neg_div hd N).const_mul C
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  have hevent : ∀ᶠ h : ℝ in 𝓝[>] 0, C * ((h ^ N)⁻¹ * Real.exp (-d / h)) < η :=
    hlim.eventually (gt_mem_nhds hη)
  filter_upwards [hevent, self_mem_nhdsWithin] with h hh hpos
  have hp : 0 < h := hpos
  intro p hP
  have hn : 0 ≤ (h ^ N)⁻¹ * Real.exp (bridgeAction b p.1 p.2 / h) *
      landauTailKernel b h p.1 p.2 ε :=
    mul_nonneg (by positivity) (landauTailKernel_nonneg hb hp p.1 p.2 ε)
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn]
  apply lt_of_le_of_lt _ hh
  have h := mul_le_mul_of_nonneg_left (hbound p.1 hP.1 p.2 hP.2 h hp)
    (show 0 ≤ (h ^ N)⁻¹ by positivity)
  nlinarith only [h]

end InfiniteZero
