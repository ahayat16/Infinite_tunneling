import InfiniteZero.ComplexLambertRoot
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic regularity of the constructed large Lambert root

Strict elementary contraction inequalities persist near the input. The
previously proved root identities and Lipschitz estimate therefore give a
continuous local inverse of `w ↦ w + log w`. The inverse-derivative theorem
then proves complex differentiability, without any analytic-branch assumption.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

/-- The open regime in which the elementary contraction bounds have slack. -/
def largeLambertRegularityDomain : Set ℂ :=
  {L | ∃ R : ℝ, 0 < R ∧ R + 2 < L.re ∧ ‖Complex.log L‖ < R / 2}

theorem eventually_largeLambert_strict_bounds {L : ℂ} {R : ℝ}
    (hR : 0 < R) (hL : R + 2 < L.re) (hlog : ‖Complex.log L‖ < R / 2) :
    ∀ᶠ M : ℂ in 𝓝 L, R + 2 < M.re ∧ ‖Complex.log M‖ < R / 2 := by
  have hslit : L ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
  exact (Complex.continuous_re.continuousAt.tendsto.eventually (lt_mem_nhds hL)).and
    ((Complex.hasDerivAt_log hslit).continuousAt.norm.tendsto.eventually (gt_mem_nhds hlog))

theorem isOpen_largeLambertRegularityDomain : IsOpen largeLambertRegularityDomain := by
  rw [isOpen_iff_mem_nhds]
  rintro L ⟨R, hR, hL, hlog⟩
  filter_upwards [eventually_largeLambert_strict_bounds hR hL hlog] with M hM
  exact ⟨R, hR, hM.1, hM.2⟩

theorem eventually_largeLambertRoot_spec {L : ℂ} {R : ℝ}
    (hR : 0 < R) (hL : R + 2 < L.re) (hlog : ‖Complex.log L‖ < R / 2) :
    ∀ᶠ M : ℂ in 𝓝 L, 2 ≤ (largeLambertRoot M).re ∧
      largeLambertRoot M + Complex.log (largeLambertRoot M) = M := by
  filter_upwards [eventually_largeLambert_strict_bounds hR hL hlog] with M hM
  have hs := largeLambertRoot_estimates hR.le hM.1.le hM.2.le
  exact ⟨hs.2.1, hs.2.2.1⟩

theorem continuousAt_largeLambertRoot {L : ℂ} {R : ℝ}
    (hR : 0 < R) (hL : R + 2 < L.re) (hlog : ‖Complex.log L‖ < R / 2) :
    ContinuousAt largeLambertRoot L := by
  have hspec := eventually_largeLambertRoot_spec hR hL hlog
  have hself := hspec.self_of_nhds
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun M : ℂ => 2 * ‖M - L‖)
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [hspec] with M hM
    exact large_complex_lambert_roots_lipschitz hM.1 hself.1 hM.2 hself.2
  · have ht : ContinuousAt (fun M : ℂ => 2 * ‖M - L‖) L := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using ht.tendsto

/-- The derivative of the actual canonical root, not of a separately assumed
analytic inverse. -/
theorem hasDerivAt_largeLambertRoot {L : ℂ} {R : ℝ}
    (hR : 0 < R) (hL : R + 2 < L.re) (hlog : ‖Complex.log L‖ < R / 2) :
    HasDerivAt largeLambertRoot
      (largeLambertRoot L / (1 + largeLambertRoot L)) L := by
  have hspec := eventually_largeLambertRoot_spec hR hL hlog
  have hw := hspec.self_of_nhds.1
  have hslit : largeLambertRoot L ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have hwne : largeLambertRoot L ≠ 0 := by
    intro he
    simp only [he, Complex.zero_re] at hw
    linarith
  have hsumne : 1 + largeLambertRoot L ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hderiv : 1 + (largeLambertRoot L)⁻¹ =
      (1 + largeLambertRoot L) / largeLambertRoot L := by
    field_simp
    ring
  have hnonzero : 1 + (largeLambertRoot L)⁻¹ ≠ 0 := by
    rw [hderiv]
    exact div_ne_zero hsumne hwne
  have hinverse := ((hasDerivAt_id (largeLambertRoot L)).add
    (Complex.hasDerivAt_log hslit)).of_local_left_inverse
      (continuousAt_largeLambertRoot hR hL hlog) hnonzero
      (hspec.mono fun _ hM => hM.2)
  convert hinverse using 1
  rw [hderiv, inv_div]

theorem differentiableOn_largeLambertRoot :
    DifferentiableOn ℂ largeLambertRoot largeLambertRegularityDomain := by
  rintro L ⟨R, hR, hL, hlog⟩
  exact (hasDerivAt_largeLambertRoot hR hL hlog).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_largeLambertRoot :
    AnalyticOnNhd ℂ largeLambertRoot largeLambertRegularityDomain :=
  differentiableOn_largeLambertRoot.analyticOnNhd isOpen_largeLambertRegularityDomain

theorem hasDerivAt_largeLambertRoot_of_mem {L : ℂ} (hL : L ∈ largeLambertRegularityDomain) :
    HasDerivAt largeLambertRoot (largeLambertRoot L / (1 + largeLambertRoot L)) L := by
  obtain ⟨R, hR, hreal, hlog⟩ := hL
  exact hasDerivAt_largeLambertRoot hR hreal hlog

/-- Differentiation with respect to the nonzero complex slope. Set
`A = tStar / (2*β)` and `d = ℓ + (k+1)/(2*β)` for the log-flat input. -/
theorem hasDerivAt_largeLambertRoot_log_mul {A c d : ℂ}
    (hc : A * c ∈ Complex.slitPlane)
    (hL : d + Complex.log (A * c) ∈ largeLambertRegularityDomain) :
    HasDerivAt (fun z : ℂ => largeLambertRoot (d + Complex.log (A * z)))
      (largeLambertRoot (d + Complex.log (A * c)) /
        (c * (1 + largeLambertRoot (d + Complex.log (A * c))))) c := by
  have hA : A ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hc)
  have hinner := (((hasDerivAt_id c).const_mul A).clog hc).const_add d
  have hcomp := (hasDerivAt_largeLambertRoot_of_mem hL).comp c hinner
  convert hcomp using 1
  simp only [mul_one, id_eq]
  rw [show A / (A * c) = c⁻¹ by rw [div_mul_eq_div_div, div_self hA, one_div]]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end InfiniteZero
