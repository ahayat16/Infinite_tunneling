import InfiniteZero.ComplexLandauAction
import InfiniteZero.LandauLaplaceTails
import InfiniteZero.LogFlatActiveWindow
import InfiniteZero.BridgeTimeRadial

/-! Actual complex proper-time tails, compared with a positive real radius.
The domain excludes a neighborhood of the unperturbed real critical time. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

def complexLandauTailKernel (b h E r ε : ℝ) (δ : ℂ) : ℂ :=
  ((b / (4 * Real.pi * h ^ 2) : ℝ) : ℂ) *
    ∫ τ in landauTailSet b E r ε, complexLandauIntegrand b h E ((r : ℂ) + δ) τ

theorem landauTailSet_subset_of_centers {b E r ρ ε : ℝ}
    (hcenter : |bridgeTime b E ρ - bridgeTime b E r| ≤ ε / 2) :
    landauTailSet b E r ε ⊆ landauTailSet b E ρ (ε / 2) := by
  intro τ hτ
  refine ⟨hτ.1, ?_⟩
  have he : τ - bridgeTime b E r =
      (τ - bridgeTime b E ρ) + (bridgeTime b E ρ - bridgeTime b E r) := by ring
  have ht := abs_add_le (τ - bridgeTime b E ρ) (bridgeTime b E ρ - bridgeTime b E r)
  rw [← he] at ht
  linarith [hτ.2]

theorem norm_complexLandauTailKernel_le {b h E r ε : ℝ} {δ : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E)
    (hr : 0 < (((r : ℂ) + δ) ^ 2).re)
    (hcenter : |bridgeTime b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) -
      bridgeTime b E r| ≤ ε / 2) :
    ‖complexLandauTailKernel b h E r ε δ‖ ≤
      landauTailKernel b h E (complexLandauEffectiveRadius ((r : ℂ) + δ)) (ε / 2) := by
  let ρ := complexLandauEffectiveRadius ((r : ℂ) + δ)
  have hρ : 0 < ρ := complexLandauEffectiveRadius_pos hr
  have hi := integrableOn_landauTailSet hb hh hE hρ (ε / 2)
  have hn : 0 ≤ᵐ[volume.restrict (landauTailSet b E ρ (ε / 2))] landauIntegrand b h E ρ := by
    filter_upwards [ae_restrict_mem (measurableSet_landauTailSet b E ρ (ε / 2))] with τ hτ
    exact (landauIntegrand_pos hb hτ.1 h E ρ).le
  unfold complexLandauTailKernel landauTailKernel
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_setIntegral_complexLandauIntegrand_le hb hr.le
    (measurableSet_landauTailSet b E r ε) (landauTailSet_subset b E r ε)).trans
      (setIntegral_mono_set hi hn
        (Eventually.of_forall (landauTailSet_subset_of_centers hcenter)))

/-- Transfer of an actual real tail bound after the correct complex action
normalization. The mismatch of real actions costs only exp(C |δ|² / h). -/
theorem norm_normalized_complexLandauTail_le
    {b h E Emax rMin rMax r ε C d : ℝ} {δ : ℂ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (hEmax : E ≤ Emax)
    (hMin : 0 < rMin) (hr : r ∈ Icc rMin rMax) (hδ : ‖δ‖ ≤ rMin / 4)
    (hcenter : |bridgeTime b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) -
      bridgeTime b E r| ≤ ε / 2)
    (htail : Real.exp (bridgeAction b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) / h) *
      landauTailKernel b h E (complexLandauEffectiveRadius ((r : ℂ) + δ)) (ε / 2) ≤
        C * Real.exp (-d / h)) :
    ‖Complex.exp (((bridgeAction b E r : ℝ) +
      ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
        complexLandauTailKernel b h E r ε δ‖ ≤
      Real.exp (complexLandauActionErrorConstant b Emax rMin rMax * ‖δ‖ ^ 2 / h) *
        (C * Real.exp (-d / h)) := by
  let ρ := complexLandauEffectiveRadius ((r : ℂ) + δ)
  let N := Complex.exp (((bridgeAction b E r : ℝ) +
    ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ))
  have hρ := (complexLandauEffectiveRadius_uniform_bounds hMin hr hδ).1
  have hn := norm_complexLandau_normalizer_relative_le hb hh hE hEmax hMin hr hδ
  have hnonneg := landauTailKernel_nonneg hb hh E ρ (ε / 2)
  have hcancellation : Real.exp (-bridgeAction b E ρ / h) *
      Real.exp (bridgeAction b E ρ / h) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  change ‖N * complexLandauTailKernel b h E r ε δ‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖N‖ * landauTailKernel b h E ρ (ε / 2) :=
      mul_le_mul_of_nonneg_left (norm_complexLandauTailKernel_le hb hh hE hρ hcenter) (norm_nonneg _)
    _ = (‖N‖ * Real.exp (-bridgeAction b E ρ / h)) *
      (Real.exp (bridgeAction b E ρ / h) * landauTailKernel b h E ρ (ε / 2)) := by
        rw [mul_assoc, ← mul_assoc (Real.exp _) (Real.exp _), hcancellation]
        simp
    _ ≤ _ := mul_le_mul hn htail
      (mul_nonneg (Real.exp_pos _).le hnonneg) (Real.exp_pos _).le

/-- Uniform exponential suppression on the shrinking complex radius window.
Both the actual tail integral and its normalizing action are retained. -/
theorem exists_uniform_normalized_complexLandauTail_bound
    {b Emin Emax rMin rMax ε tStar M : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hMin : 0 < rMin) (hMax : rMin ≤ rMax) (hε : 0 < ε) :
    ∃ C > 0, ∃ d > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rMin rMax, ∀ δ : ℂ,
      ‖δ‖ ≤ M * logFlatActiveWindow tStar h →
      ‖Complex.exp (((bridgeAction b E r : ℝ) +
        ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
          complexLandauTailKernel b h E r ε δ‖ ≤ C * Real.exp (-d / h) := by
  obtain ⟨C₀, hC₀, d, hd, htail⟩ := exists_uniform_landauTailKernel_bound hb hEmin hEmax
    (half_pos hMin) (show rMin / 2 ≤ 2 * rMax by linarith) (half_pos hε)
  let A := complexLandauActionErrorConstant b Emax rMin rMax
  have hA : 0 < A := complexLandauActionErrorConstant_pos hb (hEmin.trans_le hEmax) hMin rMax
  have hfirst : Tendsto (fun h => M * logFlatActiveWindow tStar h) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_logFlatActiveWindow tStar).const_mul M
  have hsecond : Tendsto (fun h => A * M ^ 2 * (logFlatActiveWindow tStar h ^ 2 / h))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_logFlatActiveWindow_sq_div tStar).const_mul (A * M ^ 2)
  refine ⟨Real.exp 1 * C₀, mul_pos (Real.exp_pos _) hC₀, d, hd, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    hfirst.eventually (gt_mem_nhds (show (0 : ℝ) < rMin / 4 by positivity)),
    hfirst.eventually (gt_mem_nhds (show (0 : ℝ) < ε * Real.sqrt Emin / 2 by positivity)),
    hsecond.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with h hh hrad htime hcost
  intro E hE r hr δ hδ
  have hhp : 0 < h := hh
  have hEp := hEmin.trans_le hE.1
  have hsmall : ‖δ‖ ≤ rMin / 4 := hδ.trans hrad.le
  obtain ⟨_, hρ, _, hlinear⟩ := complexLandauEffectiveRadius_uniform_bounds hMin hr hsmall
  have hcenter : |bridgeTime b E (complexLandauEffectiveRadius ((r : ℂ) + δ)) -
      bridgeTime b E r| ≤ ε / 2 := by
    apply (abs_bridgeTime_sub_le hb.ne' hEmin hE.1 _ _).trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt Emin)).mpr
    have hδtime : ‖δ‖ ≤ ε * Real.sqrt Emin / 2 := hδ.trans htime.le
    linarith
  have hnormsq : ‖δ‖ ^ 2 ≤ M ^ 2 * logFlatActiveWindow tStar h ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg δ) hδ 2
  have hcost' : A * ‖δ‖ ^ 2 / h ≤ 1 := by
    calc
      _ ≤ A * (M ^ 2 * logFlatActiveWindow tStar h ^ 2) / h := by gcongr
      _ = A * M ^ 2 * (logFlatActiveWindow tStar h ^ 2 / h) := by ring
      _ ≤ 1 := hcost.le
  apply (norm_normalized_complexLandauTail_le hb hhp hEp hE.2 hMin hr hsmall hcenter
    (htail E hE _ hρ h hhp)).trans
  calc
    _ ≤ Real.exp 1 * (C₀ * Real.exp (-d / h)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost') (by positivity)
    _ = _ := by ring

/-- Uniform smallness survives every fixed inverse integer power of h. -/
theorem eventually_normalized_complexLandauTail_small
    {b Emin Emax rMin rMax ε tStar M η : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hMin : 0 < rMin) (hMax : rMin ≤ rMax) (hε : 0 < ε)
    (N : ℕ) (hη : 0 < η) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ E ∈ Icc Emin Emax, ∀ r ∈ Icc rMin rMax, ∀ δ : ℂ,
      ‖δ‖ ≤ M * logFlatActiveWindow tStar h →
      (h ^ N)⁻¹ * ‖Complex.exp (((bridgeAction b E r : ℝ) +
        ((deriv (bridgeAction b E) r : ℝ) : ℂ) * δ) / (h : ℂ)) *
          complexLandauTailKernel b h E r ε δ‖ ≤ η := by
  obtain ⟨C, hC, d, hd, hbound⟩ := exists_uniform_normalized_complexLandauTail_bound
    (tStar := tStar) (M := M) hb hEmin hEmax hMin hMax hε
  have hlim : Tendsto (fun h : ℝ => C * ((h ^ N)⁻¹ * Real.exp (-d / h)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_inv_pow_mul_exp_neg_div hd N).const_mul C
  filter_upwards [hbound, self_mem_nhdsWithin,
    hlim.eventually (gt_mem_nhds hη)] with h hbnd hh hs
  intro E hE r hr δ hδ
  have hhp : 0 < h := hh
  have hmul := mul_le_mul_of_nonneg_left (hbnd E hE r hr δ hδ)
    (show 0 ≤ (h ^ N)⁻¹ by positivity)
  calc
    _ ≤ (h ^ N)⁻¹ * (C * Real.exp (-d / h)) := hmul
    _ = C * ((h ^ N)⁻¹ * Real.exp (-d / h)) := by ring
    _ ≤ η := hs.le

end InfiniteZero
