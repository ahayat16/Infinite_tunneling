import InfiniteZero.ComplexLandauDecomposition
import InfiniteZero.ComplexLandauWindow

/-!
# Leading asymptotic of the complex Landau kernel on the active window

The local Gaussian limit and the actual complex tail estimate are assembled
through the exact proper-time decomposition. Energy remains real and the
normalizing action is evaluated at the moving real parameters.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero

theorem tendsto_normalized_complexLandauTail_activeWindow
    {ι : Type*} {l : Filter ι} {h E r : ι → ℝ} {δ : ι → ℂ}
    {b Emin Emax rMin rMax ε tStar M : ℝ}
    (hb : 0 < b) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax)
    (hMin : 0 < rMin) (hMax : rMin ≤ rMax) (hε : 0 < ε)
    (hh : Tendsto h l (𝓝[>] 0))
    (hEbox : ∀ᶠ i in l, E i ∈ Icc Emin Emax)
    (hrbox : ∀ᶠ i in l, r i ∈ Icc rMin rMax)
    (hδ : ∀ᶠ i in l, ‖δ i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i =>
      Complex.exp (((bridgeAction b (E i) (r i) : ℂ) +
        ((deriv (bridgeAction b (E i)) (r i) : ℝ) : ℂ) * δ i) / (h i : ℂ)) *
          complexLandauTailKernel b (h i) (E i) (r i) ε (δ i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [hh.eventually (eventually_normalized_complexLandauTail_small
    (tStar := tStar) (M := M) hb hEmin hEmax hMin hMax hε 0 (half_pos hη)),
    hEbox, hrbox, hδ] with i hi hiE hir hiδ
  have hbound := hi (E i) hiE (r i) hir (δ i) hiδ
  simp only [pow_zero, inv_one, one_mul] at hbound
  simpa only [dist_zero_right] using hbound.trans_lt (half_lt_self hη)

/-- The complete, genuinely complex kernel has the real leading coefficient
on every bounded active radial window, also for moving energy and radius. -/
theorem tendsto_normalized_complexLandauKernel_activeWindow
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {δ : ι → ℂ} {b E₀ r₀ tStar M : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀))
    (hδ : ∀ᶠ i in l, ‖δ i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => ((h i * Real.sqrt (h i) : ℝ) : ℂ) *
      Complex.exp (((bridgeAction b (E i) (r i) : ℂ) +
        ((deriv (bridgeAction b (E i)) (r i) : ℝ) : ℂ) * δ i) / (h i : ℂ)) *
          complexLandauKernel b (h i) (E i) ((r i : ℂ) + δ i)) l
      (𝓝 (landauLeadingCoefficient b E₀ r₀ : ℂ)) := by
  let ε := bridgeTime b (2 * E₀) (r₀ / 2) / 2
  have hamin : 0 < bridgeTime b (2 * E₀) (r₀ / 2) :=
    bridgeTime_pos hb (by positivity) (half_pos hr₀)
  have hε : 0 < ε := half_pos hamin
  have hεa : ε < bridgeTime b (2 * E₀) (r₀ / 2) := by dsimp [ε]; linarith
  have hEbox : ∀ᶠ i in l, E i ∈ Icc (E₀ / 2) (2 * E₀) :=
    hE.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hrbox : ∀ᶠ i in l, r i ∈ Icc (r₀ / 2) (2 * r₀) :=
    hr.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hδscale := tendsto_complex_div_sqrt_of_activeWindow hh hδ
  have hlocal := (tendsto_integral_complexLandauLocalProfile_parameters hb hE₀ hr₀
    (half_pos hE₀) (half_pos hr₀) (show r₀ / 2 ≤ 2 * r₀ by linarith)
    hε hεa hh hE hr hδscale hEbox hrbox).const_mul ((b / (4 * Real.pi) : ℝ) : ℂ)
  have htail := tendsto_normalized_complexLandauTail_activeWindow hb
    (half_pos hE₀) (show E₀ / 2 ≤ 2 * E₀ by linarith)
    (half_pos hr₀) (show r₀ / 2 ≤ 2 * r₀ by linarith) hε hh hEbox hrbox hδ
  have hzero := hh.mono_right nhdsWithin_le_nhds
  have hroot : Tendsto (fun i => Real.sqrt (h i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hzero
  have hfactor : Tendsto (fun i => ((h i * Real.sqrt (h i) : ℝ) : ℂ)) l (𝓝 0) := by
    simpa only [mul_zero, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hzero.mul hroot)
  have hall := hlocal.add (hfactor.mul htail)
  have hall' : Tendsto (fun i => ((b / (4 * Real.pi) : ℝ) : ℂ) *
      (∫ u : ℝ, complexLandauLocalProfile b (E i) (r i) ε (h i) (δ i) u) +
        ((h i * Real.sqrt (h i) : ℝ) : ℂ) *
          Complex.exp (((bridgeAction b (E i) (r i) : ℂ) +
            ((deriv (bridgeAction b (E i)) (r i) : ℝ) : ℂ) * δ i) / (h i : ℂ)) *
              complexLandauTailKernel b (h i) (E i) (r i) ε (δ i)) l
        (𝓝 (landauLeadingCoefficient b E₀ r₀ : ℂ)) := by
    simpa only [zero_mul, add_zero, mul_assoc, landauLeadingCoefficient, Complex.ofReal_mul] using hall
  have hwindow : Tendsto (fun i => M * logFlatActiveWindow tStar (h i)) l (𝓝 0) := by
    simpa only [mul_zero] using ((tendsto_logFlatActiveWindow tStar).comp hh).const_mul M
  apply hall'.congr'
  filter_upwards [hEbox, hrbox, hh.eventually self_mem_nhdsWithin, hδ,
    hwindow.eventually (ge_mem_nhds (show (0 : ℝ) < (r₀ / 2) / 4 by positivity))]
      with i hiE hir hih hiδ hiw
  have hEp : 0 < E i := (half_pos hE₀).trans_le hiE.1
  have hrp : 0 < r i := (half_pos hr₀).trans_le hir.1
  have hea : ε < bridgeTime b (E i) (r i) := hεa.trans_le
    (bridgeTime_mem_uniform_Icc hb (half_pos hE₀) (half_pos hr₀) hiE hir).1
  have hQ := (complexLandauEffectiveRadius_uniform_bounds (half_pos hr₀) hir (hiδ.trans hiw)).1
  exact (normalized_complexLandauKernel_decomposition hb hEp hrp hea hih hQ).symm

theorem tendsto_h_three_halves_normalized_complexLandauKernel_activeWindow
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {δ : ι → ℂ} {b E₀ r₀ tStar M : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀))
    (hδ : ∀ᶠ i in l, ‖δ i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => (((h i) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (((bridgeAction b (E i) (r i) : ℂ) +
        ((deriv (bridgeAction b (E i)) (r i) : ℝ) : ℂ) * δ i) / (h i : ℂ)) *
          complexLandauKernel b (h i) (E i) ((r i : ℂ) + δ i)) l
      (𝓝 (landauLeadingCoefficient b E₀ r₀ : ℂ)) := by
  apply (tendsto_normalized_complexLandauKernel_activeWindow hb hE₀ hr₀ hh hE hr hδ).congr'
  filter_upwards [hh.eventually self_mem_nhdsWithin] with i hi
  have hip : 0 < h i := hi
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hip,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem tendsto_complexLandauKernel_relative_activeWindow
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {δ : ι → ℂ} {b E₀ r₀ tStar M : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀))
    (hδ : ∀ᶠ i in l, ‖δ i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => ((((h i) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (((bridgeAction b (E i) (r i) : ℂ) +
        ((deriv (bridgeAction b (E i)) (r i) : ℝ) : ℂ) * δ i) / (h i : ℂ)) *
          complexLandauKernel b (h i) (E i) ((r i : ℂ) + δ i)) /
            (landauLeadingCoefficient b (E i) (r i) : ℂ)) l (𝓝 1) := by
  have hne : (landauLeadingCoefficient b E₀ r₀ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (landauLeadingCoefficient_pos hb hE₀ hr₀).ne'
  have hk := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_landauLeadingCoefficient_parameters hb hE₀ hr₀ hE hr)
  simpa only [div_self hne] using
    (tendsto_h_three_halves_normalized_complexLandauKernel_activeWindow hb hE₀ hr₀ hh hE hr hδ).div hk hne

private theorem eventually_window_mul_bound
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {ξ : ι → ℂ} {ξ₀ : ℂ} {tStar : ℝ}
    (ht : 0 < tStar) (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    ∀ᶠ i in l, ‖(logFlatActiveWindow tStar (h i) : ℂ) * ξ i‖ ≤
      (‖ξ₀‖ + 1) * logFlatActiveWindow tStar (h i) := by
  filter_upwards [hξ.norm.eventually (ge_mem_nhds (by linarith : ‖ξ₀‖ < ‖ξ₀‖ + 1))] with i hi
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logFlatActiveWindow_pos ht _).le]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (logFlatActiveWindow_pos ht _).le

/-- The rescaled complex displacement may itself move. -/
theorem tendsto_complexLandauKernel_window_parameters
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {ξ : ι → ℂ} {b E₀ r₀ tStar : ℝ} {ξ₀ : ℂ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀) (ht : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀)) (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun i => (((h i) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (((bridgeAction b (E i) (r i) : ℂ) +
        ((deriv (bridgeAction b (E i)) (r i) : ℝ) : ℂ) *
          ((logFlatActiveWindow tStar (h i) : ℂ) * ξ i)) / (h i : ℂ)) *
          complexLandauKernel b (h i) (E i)
            ((r i : ℂ) + (logFlatActiveWindow tStar (h i) : ℂ) * ξ i)) l
      (𝓝 (landauLeadingCoefficient b E₀ r₀ : ℂ)) :=
  tendsto_h_three_halves_normalized_complexLandauKernel_activeWindow hb hE₀ hr₀ hh hE hr
    (eventually_window_mul_bound ht hξ)

theorem tendsto_complexLandauKernel_relative_window_parameters
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {ξ : ι → ℂ} {b E₀ r₀ tStar : ℝ} {ξ₀ : ℂ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hr₀ : 0 < r₀) (ht : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : Tendsto r l (𝓝 r₀)) (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun i => ((((h i) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (((bridgeAction b (E i) (r i) : ℂ) +
        ((deriv (bridgeAction b (E i)) (r i) : ℝ) : ℂ) *
          ((logFlatActiveWindow tStar (h i) : ℂ) * ξ i)) / (h i : ℂ)) *
          complexLandauKernel b (h i) (E i)
            ((r i : ℂ) + (logFlatActiveWindow tStar (h i) : ℂ) * ξ i)) /
            (landauLeadingCoefficient b (E i) (r i) : ℂ)) l (𝓝 1) :=
  tendsto_complexLandauKernel_relative_activeWindow hb hE₀ hr₀ hh hE hr
    (eventually_window_mul_bound ht hξ)

theorem tendstoLocallyUniformlyOn_complexLandauKernel_leading
    {b tStar : ℝ} (hb : 0 < b) (ht : 0 < tStar) :
    TendstoLocallyUniformlyOn
      (fun h (p : (ℝ × ℝ) × ℂ) => ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b p.1.1 p.1.2 : ℂ) +
          ((deriv (bridgeAction b p.1.1) p.1.2 : ℝ) : ℂ) *
            ((logFlatActiveWindow tStar h : ℂ) * p.2)) / (h : ℂ)) *
          complexLandauKernel b h p.1.1 ((p.1.2 : ℂ) + (logFlatActiveWindow tStar h : ℂ) * p.2))
      (fun p => (landauLeadingCoefficient b p.1.1 p.1.2 : ℂ)) (𝓝[>] 0)
      ((Ioi 0 ×ˢ Ioi 0) ×ˢ (univ : Set ℂ)) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro p hp
  have hpar : Tendsto (fun q : ℝ × ((ℝ × ℝ) × ℂ) => q.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝[(Ioi 0 ×ˢ Ioi 0) ×ˢ (univ : Set ℂ)] p) (𝓝 p) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hE := ((show Continuous (fun q : (ℝ × ℝ) × ℂ => q.1.1) by fun_prop).tendsto p).comp hpar
  have hr := ((show Continuous (fun q : (ℝ × ℝ) × ℂ => q.1.2) by fun_prop).tendsto p).comp hpar
  have hξ := (continuous_snd.tendsto p).comp hpar
  have hk := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_landauLeadingCoefficient_parameters hb hp.1.1 hp.1.2 hE hr)
  have hmain := tendsto_complexLandauKernel_window_parameters hb hp.1.1 hp.1.2 ht
    tendsto_fst hE hr hξ
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  simpa only [dist_self] using hk.dist hmain

/-- Uniform leading asymptotic on every compact positive real parameter set
and compact set of rescaled complex radial displacements. -/
theorem tendstoUniformlyOn_complexLandauKernel_leading
    {b tStar : ℝ} (hb : 0 < b) (ht : 0 < tStar)
    {K : Set ((ℝ × ℝ) × ℂ)} (hK : IsCompact K)
    (hKpos : K ⊆ (Ioi 0 ×ˢ Ioi 0) ×ˢ (univ : Set ℂ)) :
    TendstoUniformlyOn
      (fun h (p : (ℝ × ℝ) × ℂ) => ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b p.1.1 p.1.2 : ℂ) +
          ((deriv (bridgeAction b p.1.1) p.1.2 : ℝ) : ℂ) *
            ((logFlatActiveWindow tStar h : ℂ) * p.2)) / (h : ℂ)) *
          complexLandauKernel b h p.1.1 ((p.1.2 : ℂ) + (logFlatActiveWindow tStar h : ℂ) * p.2))
      (fun p => (landauLeadingCoefficient b p.1.1 p.1.2 : ℂ)) (𝓝[>] 0) K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((tendstoLocallyUniformlyOn_complexLandauKernel_leading hb ht).mono hKpos)

/-- The nonzero real leading coefficient gives a uniform relative `1 + o(1)`
for the actual complex proper-time integral on the shrinking window. -/
theorem tendstoUniformlyOn_complexLandauKernel_relative
    {b tStar : ℝ} (hb : 0 < b) (ht : 0 < tStar)
    {K : Set ((ℝ × ℝ) × ℂ)} (hK : IsCompact K)
    (hKpos : K ⊆ (Ioi 0 ×ˢ Ioi 0) ×ˢ (univ : Set ℂ)) :
    TendstoUniformlyOn
      (fun h (p : (ℝ × ℝ) × ℂ) => (((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b p.1.1 p.1.2 : ℂ) +
          ((deriv (bridgeAction b p.1.1) p.1.2 : ℝ) : ℂ) *
            ((logFlatActiveWindow tStar h : ℂ) * p.2)) / (h : ℂ)) *
          complexLandauKernel b h p.1.1 ((p.1.2 : ℂ) + (logFlatActiveWindow tStar h : ℂ) * p.2)) /
            (landauLeadingCoefficient b p.1.1 p.1.2 : ℂ))
      (fun _ => 1) (𝓝[>] 0) K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro p hp
  have hp' := hKpos hp
  have hpar : Tendsto (fun q : ℝ × ((ℝ × ℝ) × ℂ) => q.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝[K] p) (𝓝 p) := tendsto_snd.mono_right nhdsWithin_le_nhds
  have hE := ((show Continuous (fun q : (ℝ × ℝ) × ℂ => q.1.1) by fun_prop).tendsto p).comp hpar
  have hr := ((show Continuous (fun q : (ℝ × ℝ) × ℂ => q.1.2) by fun_prop).tendsto p).comp hpar
  have hξ := (continuous_snd.tendsto p).comp hpar
  exact Uniform.tendsto_nhds_right.mp
    (tendsto_complexLandauKernel_relative_window_parameters hb hp'.1.1 hp'.1.2 ht
      tendsto_fst hE hr hξ)

theorem tendstoUniformlyOn_complexLandauKernel_relative_rectangle
    {b tStar Emin Emax rmin rmax M : ℝ}
    (hb : 0 < b) (ht : 0 < tStar) (hEmin : 0 < Emin) (hrmin : 0 < rmin) :
    TendstoUniformlyOn
      (fun h (p : (ℝ × ℝ) × ℂ) => (((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((bridgeAction b p.1.1 p.1.2 : ℂ) +
          ((deriv (bridgeAction b p.1.1) p.1.2 : ℝ) : ℂ) *
            ((logFlatActiveWindow tStar h : ℂ) * p.2)) / (h : ℂ)) *
          complexLandauKernel b h p.1.1 ((p.1.2 : ℂ) + (logFlatActiveWindow tStar h : ℂ) * p.2)) /
            (landauLeadingCoefficient b p.1.1 p.1.2 : ℂ))
      (fun _ => 1) (𝓝[>] 0)
      ((Icc Emin Emax ×ˢ Icc rmin rmax) ×ˢ Metric.closedBall (0 : ℂ) M) := by
  apply tendstoUniformlyOn_complexLandauKernel_relative hb ht
    ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _))
  intro p hp
  exact ⟨⟨hEmin.trans_le hp.1.1.1, hrmin.trans_le hp.1.2.1⟩, mem_univ _⟩

end InfiniteZero
