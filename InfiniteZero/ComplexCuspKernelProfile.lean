import InfiniteZero.ComplexLandauAsymptotic
import InfiniteZero.ComplexCuspRemainder

/-!
# The actual complex Landau kernel on polynomial cusp charts

The normalizing action uses the linear normal displacements `t / 2` and
`(t + u) / 2`. The errors in those displacements are proved from the actual
charts, uniformly in bounded tangential parameters. Their quotient by `h`
tends to zero on the active normal window.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

/-- Relative kernel profile at the actual complex radius `z`, normalized by
the specified linear displacement `ℓ` from the positive real radius `R`. -/
def complexLandauLinearizedProfile (b h E R : ℝ) (z ℓ : ℂ) : ℂ :=
  (((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
    Complex.exp (((bridgeAction b E R : ℂ) +
      ((deriv (bridgeAction b E) R : ℝ) : ℂ) * ℓ) / (h : ℂ)) *
    complexLandauKernel b h E z) / (landauLeadingCoefficient b E R : ℂ)

private theorem radial_remainder_control
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {z ℓ : ι → ℂ}
    {R tStar A C : ℝ} (htStar : 0 < tStar) (hC : 0 ≤ C)
    (hh : Tendsto h l (𝓝[>] 0))
    (hlin : ∀ᶠ i in l, ‖ℓ i‖ ≤ A * logFlatActiveWindow tStar (h i))
    (hrem : ∀ᶠ i in l, ‖z i - (R : ℂ) - ℓ i‖ ≤
      C * logFlatActiveWindow tStar (h i) ^ 2) :
    (∀ᶠ i in l, ‖z i - (R : ℂ)‖ ≤ (A + C) * logFlatActiveWindow tStar (h i)) ∧
      Tendsto (fun i => (z i - (R : ℂ) - ℓ i) / (h i : ℂ)) l (𝓝 0) := by
  constructor
  · filter_upwards [hlin, hrem, ((tendsto_logFlatActiveWindow tStar).comp hh).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with i hi hr hw
    change logFlatActiveWindow tStar (h i) ≤ 1 at hw
    have hw0 := (logFlatActiveWindow_pos htStar (h i)).le
    have hsq : logFlatActiveWindow tStar (h i) ^ 2 ≤ logFlatActiveWindow tStar (h i) := by
      nlinarith
    have hn := norm_add_le (z i - (R : ℂ) - ℓ i) (ℓ i)
    rw [sub_add_cancel] at hn
    nlinarith [mul_le_mul_of_nonneg_left hsq hC]
  · apply squeeze_zero_norm' (a := fun i => C *
      (logFlatActiveWindow tStar (h i) ^ 2 / h i)) ?_ ?_
    · filter_upwards [hrem, hh.eventually self_mem_nhdsWithin] with i hi hhi
      have hp : 0 < h i := hhi
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le]
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hi hp.le
    · simpa using ((tendsto_logFlatActiveWindow_sq_div tStar).comp hh).const_mul C

private theorem tendsto_linearized_profile_of_remainder
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E : ι → ℝ} {z ℓ : ι → ℂ} {b E₀ R tStar M : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hR : 0 < R)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hz : ∀ᶠ i in l, ‖z i - (R : ℂ)‖ ≤ M * logFlatActiveWindow tStar (h i))
    (hrem : Tendsto (fun i => (z i - (R : ℂ) - ℓ i) / (h i : ℂ)) l (𝓝 0)) :
    Tendsto (fun i => complexLandauLinearizedProfile b (h i) (E i) R (z i) (ℓ i))
      l (𝓝 1) := by
  have hj : Tendsto (fun i => ((deriv (bridgeAction b (E i)) R : ℝ) : ℂ)) l
      (𝓝 ((Real.sqrt (b ^ 2 * R ^ 2 + 4 * E₀) / 2 : ℝ) : ℂ)) := by
    have hc : Continuous (fun e : ℝ =>
        ((Real.sqrt (b ^ 2 * R ^ 2 + 4 * e) / 2 : ℝ) : ℂ)) := by fun_prop
    apply ((hc.tendsto E₀).comp hE).congr'
    filter_upwards [hE.eventually (lt_mem_nhds hE₀)] with i hi
    rw [deriv_bridgeAction hb.ne' hi]
    rfl
  have hexp : Tendsto (fun i => Complex.exp
      (-((deriv (bridgeAction b (E i)) R : ℝ) : ℂ) *
        ((z i - (R : ℂ) - ℓ i) / (h i : ℂ)))) l (𝓝 1) := by
    simpa using Complex.continuous_exp.continuousAt.tendsto.comp (hj.neg.mul hrem)
  have hmain := tendsto_complexLandauKernel_relative_activeWindow hb hE₀ hR hh hE
    (tendsto_const_nhds : Tendsto (fun _ : ι => R) l (𝓝 R)) hz
  have hprod := hexp.mul hmain
  simp only [mul_one] at hprod
  apply hprod.congr'
  exact Eventually.of_forall fun i => by
    dsimp only [complexLandauLinearizedProfile]
    rw [add_sub_cancel]
    let H : ℂ := ((h i) ^ (3 / 2 : ℝ) : ℝ)
    let J : ℂ := bridgeAction b (E i) R
    let j : ℂ := ((deriv (bridgeAction b (E i)) R : ℝ) : ℂ)
    let K := complexLandauKernel b (h i) (E i) (z i)
    let k : ℂ := landauLeadingCoefficient b (E i) R
    have he : Complex.exp (-j * ((z i - (R : ℂ) - ℓ i) / (h i : ℂ))) *
        Complex.exp ((J + j * (z i - (R : ℂ))) / (h i : ℂ)) =
        Complex.exp ((J + j * ℓ i) / (h i : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    change Complex.exp (-j * ((z i - (R : ℂ) - ℓ i) / (h i : ℂ))) *
      (H * Complex.exp ((J + j * (z i - (R : ℂ))) / (h i : ℂ)) * K / k) =
      H * Complex.exp ((J + j * ℓ i) / (h i : ℂ)) * K / k
    calc
      _ = H * (Complex.exp (-j * ((z i - (R : ℂ) - ℓ i) / (h i : ℂ))) *
        Complex.exp ((J + j * (z i - (R : ℂ))) / (h i : ℂ))) * K / k := by ring
      _ = _ := by rw [he]

namespace Geometry

/-- The true source radius has a uniformly negligible quadratic remainder. -/
theorem complexCuspPlus_radius_activeWindow_control
    {ι : Type*} {l : Filter ι} {h s : ι → ℝ} {t : ι → ℂ}
    {R s₀ tStar M : ℝ} (hR : 0 < R) (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0))
    (hs : ∀ᶠ i in l, |s i| ≤ s₀)
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    (∀ᶠ i in l,
      ‖complexRadius (complexCuspPlus R (s i) (t i)) - (R : ℂ)‖ ≤
        (M / 2 + sourceRadiusRemainderConstant R s₀ * M ^ 2) *
          logFlatActiveWindow tStar (h i)) ∧
    Tendsto (fun i => (complexRadius (complexCuspPlus R (s i) (t i)) -
      (R : ℂ) - t i / 2) / (h i : ℂ)) l (𝓝 0) := by
  have hW : Tendsto (fun i => M * logFlatActiveWindow tStar (h i)) l (𝓝 0) := by
    simpa using ((tendsto_logFlatActiveWindow tStar).comp hh).const_mul M
  apply radial_remainder_control htStar
    (mul_nonneg (sourceRadiusRemainderConstant_pos hR hs₀).le (sq_nonneg M)) hh
  · filter_upwards [ht] with i hi
    rw [norm_div, Complex.norm_ofNat]
    nlinarith
  · filter_upwards [hs, ht,
      hW.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hW.eventually (ge_mem_nhds hR)] with i hsi hti hw1 hwR
    have hb := norm_complexRadius_cuspPlus_remainder_le hR hs₀ hsi
      (hti.trans hw1) (hti.trans hwR)
    have hsq := pow_le_pow_left₀ (norm_nonneg (t i)) hti 2
    rw [mul_pow] at hsq
    exact hb.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsq
        (sourceRadiusRemainderConstant_pos hR hs₀).le)

/-- The actual bridge radius has a uniformly negligible quadratic remainder. -/
theorem complexCuspBridge_radius_activeWindow_control
    {ι : Type*} {l : Filter ι} {h s r : ι → ℝ} {t u : ι → ℂ}
    {R L s₀ tStar M : ℝ} (hL : R < 2 * L) (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0))
    (hs : ∀ᶠ i in l, |s i| ≤ s₀) (hr : ∀ᶠ i in l, |r i| ≤ s₀)
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ M * logFlatActiveWindow tStar (h i))
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    (∀ᶠ i in l,
      ‖complexRadius (complexBridge L (complexCuspPlus R (s i) (t i))
        (complexCuspMinus R (r i) (u i))) - (activeDistance R L : ℂ)‖ ≤
        (M + 2 * bridgeRadiusRemainderConstant (activeDistance R L) s₀ * M ^ 2) *
          logFlatActiveWindow tStar (h i)) ∧
    Tendsto (fun i => (complexRadius (complexBridge L (complexCuspPlus R (s i) (t i))
      (complexCuspMinus R (r i) (u i))) - (activeDistance R L : ℂ) -
        (t i + u i) / 2) / (h i : ℂ)) l (𝓝 0) := by
  have hD := activeDistance_pos hL
  have hC := bridgeRadiusRemainderConstant_pos hD hs₀
  have hW : Tendsto (fun i => M * logFlatActiveWindow tStar (h i)) l (𝓝 0) := by
    simpa using ((tendsto_logFlatActiveWindow tStar).comp hh).const_mul M
  apply radial_remainder_control htStar (by positivity) hh
  · filter_upwards [ht, hu] with i hti hui
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le (t i) (u i)
    linarith
  · filter_upwards [hs, hr, ht, hu,
      hW.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hW.eventually (ge_mem_nhds (half_pos hD))] with i hsi hri hti hui hw1 hwD
    have hb := norm_complexRadius_bridge_remainder_le hL hs₀ hsi hri
      (hti.trans hw1) (hui.trans hw1) (hti.trans hwD) (hui.trans hwD)
    have htsq := pow_le_pow_left₀ (norm_nonneg (t i)) hti 2
    have husq := pow_le_pow_left₀ (norm_nonneg (u i)) hui 2
    rw [mul_pow] at htsq husq
    apply hb.trans
    nlinarith [mul_le_mul_of_nonneg_left htsq hC.le,
      mul_le_mul_of_nonneg_left husq hC.le]

/-- The true plus-source kernel has relative leading coefficient one when
normalized by its normal first-order displacement. Tangential parameters
need only remain bounded, and the real energy may move without a prescribed rate. -/
theorem tendsto_complexCuspPlus_kernel_relative
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E s : ι → ℝ} {t : ι → ℂ} {b E₀ R s₀ tStar M : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hR : 0 < R)
    (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hs : ∀ᶠ i in l, |s i| ≤ s₀)
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => complexLandauLinearizedProfile b (h i) (E i) R
      (complexRadius (complexCuspPlus R (s i) (t i))) (t i / 2)) l (𝓝 1) := by
  obtain ⟨hwindow, hrem⟩ := complexCuspPlus_radius_activeWindow_control hR hs₀ htStar hh hs ht
  exact tendsto_linearized_profile_of_remainder hb hE₀ hR hh hE hwindow hrem

/-- The corresponding minus-source kernel obeys the same actual-radius result. -/
theorem tendsto_complexCuspMinus_kernel_relative
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E r : ι → ℝ} {u : ι → ℂ} {b E₀ R s₀ tStar M : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hR : 0 < R)
    (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hr : ∀ᶠ i in l, |r i| ≤ s₀)
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => complexLandauLinearizedProfile b (h i) (E i) R
      (complexRadius (complexCuspMinus R (r i) (u i))) (u i / 2)) l (𝓝 1) := by
  simpa only [complexRadius_cuspMinus_eq_plus] using
    tendsto_complexCuspPlus_kernel_relative hb hE₀ hR hs₀ htStar hh hE hr hu

/-- The actual bridge kernel is normalized by `(t + u) / 2`, with no assumed
radius remainder and no convergence assumption on the tangential parameters. -/
theorem tendsto_complexCuspBridge_kernel_relative
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h E s r : ι → ℝ} {t u : ι → ℂ} {b E₀ R L s₀ tStar M : ℝ}
    (hb : 0 < b) (hE₀ : 0 < E₀) (hL : R < 2 * L)
    (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0)) (hE : Tendsto E l (𝓝 E₀))
    (hs : ∀ᶠ i in l, |s i| ≤ s₀) (hr : ∀ᶠ i in l, |r i| ≤ s₀)
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ M * logFlatActiveWindow tStar (h i))
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => complexLandauLinearizedProfile b (h i) (E i) (activeDistance R L)
      (complexRadius (complexBridge L (complexCuspPlus R (s i) (t i))
        (complexCuspMinus R (r i) (u i)))) ((t i + u i) / 2)) l (𝓝 1) := by
  obtain ⟨hwindow, hrem⟩ :=
    complexCuspBridge_radius_activeWindow_control hL hs₀ htStar hh hs hr ht hu
  exact tendsto_linearized_profile_of_remainder hb hE₀ (activeDistance_pos hL)
    hh hE hwindow hrem

end Geometry
end InfiniteZero
