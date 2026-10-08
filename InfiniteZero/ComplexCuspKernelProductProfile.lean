import InfiniteZero.ComplexCuspKernelProfile
import InfiniteZero.ComplexCuspPhase
import InfiniteZero.ComplexCuspKernelHolomorphic

/-!
# Uniform relative profile of the three genuine kernels and magnetic phase

The two source kernels use the same moving core energy, and the bridge
kernel uses the independently moving full energy. The actual complex radii
and magnetic phase are retained. Only their normal linear terms enter the
normalization; no energy slope is frozen in this module.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero.Geometry

/-- Product of the three actual-radius relative kernel profiles and the
correction for the exact quadratic and higher magnetic phase. -/
def complexCuspKernelPhaseProfile (b h Ecore Efull R L s r : ℝ) (t u : ℂ) : ℂ :=
  complexLandauLinearizedProfile b h Ecore R
      (complexRadius (complexCuspPlus R s t)) (t / 2) *
    complexLandauLinearizedProfile b h Ecore R
      (complexRadius (complexCuspMinus R r u)) (u / 2) *
    complexLandauLinearizedProfile b h Efull (activeDistance R L)
      (complexRadius (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r u)))
      ((t + u) / 2) *
    Complex.exp (Complex.I * complexCuspPhaseRemainder b R L s r t u / (h : ℂ))

/-- Exact relation with the product of the three true kernels and the full
magnetic phase. Both real action derivatives still use their moving energies. -/
theorem complexCuspKernelPhaseProfile_eq_normalized_product
    (b h Ecore Efull R L s r : ℝ) (t u : ℂ) :
    complexCuspKernelPhaseProfile b h Ecore Efull R L s r t u =
      ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 3 /
        ((landauLeadingCoefficient b Ecore R : ℂ) ^ 2 *
          (landauLeadingCoefficient b Efull (activeDistance R L) : ℂ)) *
      Complex.exp ((2 * (bridgeAction b Ecore R : ℂ) +
        (bridgeAction b Efull (activeDistance R L) : ℂ) +
        ((((deriv (bridgeAction b Ecore) R : ℝ) : ℂ) +
          ((deriv (bridgeAction b Efull) (activeDistance R L) : ℝ) : ℂ)) / 2 -
            Complex.I * (phaseSlope b L : ℂ)) * (t + u) -
        Complex.I * (phaseStar b R L : ℂ)) / (h : ℂ)) *
      (complexCuspKernelProduct b h Ecore Ecore Efull R L s r (t, u) *
        Complex.exp (Complex.I *
          complexPhase b L (complexCuspPlus R s t) (complexCuspMinus R r u) / (h : ℂ))) := by
  have he :
      Complex.exp (((bridgeAction b Ecore R : ℂ) +
        ((deriv (bridgeAction b Ecore) R : ℝ) : ℂ) * (t / 2)) / (h : ℂ)) *
      Complex.exp (((bridgeAction b Ecore R : ℂ) +
        ((deriv (bridgeAction b Ecore) R : ℝ) : ℂ) * (u / 2)) / (h : ℂ)) *
      Complex.exp (((bridgeAction b Efull (activeDistance R L) : ℂ) +
        ((deriv (bridgeAction b Efull) (activeDistance R L) : ℝ) : ℂ) *
          ((t + u) / 2)) / (h : ℂ)) *
      Complex.exp (Complex.I * complexCuspPhaseRemainder b R L s r t u / (h : ℂ)) =
      Complex.exp ((2 * (bridgeAction b Ecore R : ℂ) +
        (bridgeAction b Efull (activeDistance R L) : ℂ) +
        ((((deriv (bridgeAction b Ecore) R : ℝ) : ℂ) +
          ((deriv (bridgeAction b Efull) (activeDistance R L) : ℝ) : ℂ)) / 2 -
            Complex.I * (phaseSlope b L : ℂ)) * (t + u) -
        Complex.I * (phaseStar b R L : ℂ)) / (h : ℂ)) *
      Complex.exp (Complex.I *
        complexPhase b L (complexCuspPlus R s t) (complexCuspMinus R r u) / (h : ℂ)) := by
    simp only [← Complex.exp_add]
    congr 1
    unfold complexCuspPhaseRemainder
    ring
  calc
    _ = ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 3 /
        ((landauLeadingCoefficient b Ecore R : ℂ) ^ 2 *
          (landauLeadingCoefficient b Efull (activeDistance R L) : ℂ)) *
      (Complex.exp (((bridgeAction b Ecore R : ℂ) +
        ((deriv (bridgeAction b Ecore) R : ℝ) : ℂ) * (t / 2)) / (h : ℂ)) *
      Complex.exp (((bridgeAction b Ecore R : ℂ) +
        ((deriv (bridgeAction b Ecore) R : ℝ) : ℂ) * (u / 2)) / (h : ℂ)) *
      Complex.exp (((bridgeAction b Efull (activeDistance R L) : ℂ) +
        ((deriv (bridgeAction b Efull) (activeDistance R L) : ℝ) : ℂ) *
          ((t + u) / 2)) / (h : ℂ)) *
      Complex.exp (Complex.I * complexCuspPhaseRemainder b R L s r t u / (h : ℂ))) *
      complexCuspKernelProduct b h Ecore Ecore Efull R L s r (t, u) := by
        simp only [complexCuspKernelPhaseProfile, complexLandauLinearizedProfile,
          complexCuspKernelProduct, complexCuspPlusKernel, complexCuspMinusKernel,
          complexCuspBridgeKernel, div_eq_mul_inv, mul_inv_rev]
        ring
    _ = _ := by rw [he]; ring

/-- Relative convergence along arbitrary paths in the shrinking complex
normal window. Tangential parameters are only required to remain bounded. -/
theorem tendsto_complexCuspKernelPhaseProfile
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {h Ecore Efull s r : ι → ℝ} {t u : ι → ℂ}
    {b Ecore₀ Efull₀ R L s₀ tStar M : ℝ}
    (hb : 0 < b) (hEc : 0 < Ecore₀) (hEf : 0 < Efull₀)
    (hR : 0 < R) (hL : R < 2 * L) (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hh : Tendsto h l (𝓝[>] 0))
    (hcore : Tendsto Ecore l (𝓝 Ecore₀)) (hfull : Tendsto Efull l (𝓝 Efull₀))
    (hs : ∀ᶠ i in l, |s i| ≤ s₀) (hr : ∀ᶠ i in l, |r i| ≤ s₀)
    (ht : ∀ᶠ i in l, ‖t i‖ ≤ M * logFlatActiveWindow tStar (h i))
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M * logFlatActiveWindow tStar (h i)) :
    Tendsto (fun i => complexCuspKernelPhaseProfile b (h i) (Ecore i) (Efull i)
      R L (s i) (r i) (t i) (u i)) l (𝓝 1) := by
  have hp := tendsto_complexCuspPlus_kernel_relative hb hEc hR hs₀ htStar hh hcore hs ht
  have hm := tendsto_complexCuspMinus_kernel_relative hb hEc hR hs₀ htStar hh hcore hr hu
  have hbr := tendsto_complexCuspBridge_kernel_relative hb hEf hL hs₀ htStar
    hh hfull hs hr ht hu
  have hphase := tendsto_complexCuspPhase_correction (b := b) (R := R) (L := L)
    hs₀ hh hs hr ht hu
  simpa only [complexCuspKernelPhaseProfile, complexCuspPhaseRemainder, one_mul] using
    ((hp.mul hm).mul hbr).mul hphase

/-- A single sufficiently small `h` works for all tangential coordinates
and all complex normal coordinates in the active window. -/
theorem eventually_complexCuspKernelPhaseProfile_uniform
    {Ecore Efull : ℝ → ℝ} {b Ecore₀ Efull₀ R L s₀ tStar M : ℝ}
    (hb : 0 < b) (hEc : 0 < Ecore₀) (hEf : 0 < Efull₀)
    (hR : 0 < R) (hL : R < 2 * L) (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hcore : Tendsto Ecore (𝓝[>] 0) (𝓝 Ecore₀))
    (hfull : Tendsto Efull (𝓝[>] 0) (𝓝 Efull₀)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ s₀ → |r| ≤ s₀ →
      ∀ t u : ℂ, ‖t‖ ≤ M * logFlatActiveWindow tStar h →
        ‖u‖ ≤ M * logFlatActiveWindow tStar h →
        ‖complexCuspKernelPhaseProfile b h (Ecore h) (Efull h) R L s r t u - 1‖ < ε := by
  let P := ℝ × (ℝ × ℝ) × (ℂ × ℂ)
  let S : Set P := {q | |q.2.1.1| ≤ s₀ ∧ |q.2.1.2| ≤ s₀ ∧
    ‖q.2.2.1‖ ≤ M * logFlatActiveWindow tStar q.1 ∧
    ‖q.2.2.2‖ ≤ M * logFlatActiveWindow tStar q.1}
  let l : Filter P := Filter.comap Prod.fst (𝓝[>] (0 : ℝ)) ⊓ 𝓟 S
  have hh : Tendsto (fun q : P => q.1) l (𝓝[>] (0 : ℝ)) :=
    tendsto_comap.mono_left inf_le_left
  have hS : ∀ᶠ q in l, q ∈ S := by
    exact (show ∀ᶠ q in 𝓟 S, q ∈ S from eventually_principal.mpr (fun _ hq => hq)).filter_mono
      inf_le_right
  have hs : ∀ᶠ q in l, |q.2.1.1| ≤ s₀ := hS.mono (fun _ hq => hq.1)
  have hr : ∀ᶠ q in l, |q.2.1.2| ≤ s₀ := hS.mono (fun _ hq => hq.2.1)
  have ht : ∀ᶠ q in l, ‖q.2.2.1‖ ≤ M * logFlatActiveWindow tStar q.1 :=
    hS.mono (fun _ hq => hq.2.2.1)
  have hu : ∀ᶠ q in l, ‖q.2.2.2‖ ≤ M * logFlatActiveWindow tStar q.1 :=
    hS.mono (fun _ hq => hq.2.2.2)
  have hlim := tendsto_complexCuspKernelPhaseProfile hb hEc hEf hR hL hs₀ htStar
    hh (hcore.comp hh) (hfull.comp hh) hs hr ht hu
  have he := (Metric.tendsto_nhds.mp hlim) ε hε
  simp only [dist_eq_norm] at he
  have he' := eventually_comap.mp (eventually_inf_principal.mp he)
  filter_upwards [he'] with h hh'
  intro s r hs hr t u ht hu
  exact hh' (h, (s, r), (t, u)) rfl ⟨hs, hr, ht, hu⟩

/-- In particular, the normalized product is uniformly bounded by two on
the whole active complex window. -/
theorem eventually_norm_complexCuspKernelPhaseProfile_le_two
    {Ecore Efull : ℝ → ℝ} {b Ecore₀ Efull₀ R L s₀ tStar M : ℝ}
    (hb : 0 < b) (hEc : 0 < Ecore₀) (hEf : 0 < Efull₀)
    (hR : 0 < R) (hL : R < 2 * L) (hs₀ : 0 ≤ s₀) (htStar : 0 < tStar)
    (hcore : Tendsto Ecore (𝓝[>] 0) (𝓝 Ecore₀))
    (hfull : Tendsto Efull (𝓝[>] 0) (𝓝 Efull₀)) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ s₀ → |r| ≤ s₀ →
      ∀ t u : ℂ, ‖t‖ ≤ M * logFlatActiveWindow tStar h →
        ‖u‖ ≤ M * logFlatActiveWindow tStar h →
        ‖complexCuspKernelPhaseProfile b h (Ecore h) (Efull h) R L s r t u‖ ≤ 2 := by
  filter_upwards [eventually_complexCuspKernelPhaseProfile_uniform
    (M := M) hb hEc hEf hR hL hs₀ htStar hcore hfull (by norm_num : (0 : ℝ) < 1)] with h hh
  intro s r hs hr t u ht hu
  have he := hh s r hs hr t u ht hu
  have hn := norm_sub_le (complexCuspKernelPhaseProfile b h (Ecore h) (Efull h)
    R L s r t u - 1) (-1)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at hn
  linarith

end InfiniteZero.Geometry
