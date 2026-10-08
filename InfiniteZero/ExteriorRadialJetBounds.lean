import InfiniteZero.LandauKernelEquationOffDiagonal
import InfiniteZero.LandauSpatialDerivativeBounds

/-!
# Jets of the same wavefunction from its exact exterior radial tail

An equality on the open exterior region identifies every Fréchet jet at
each exterior point. The real-to-complex embedding is isometric, so its
presence changes neither the derivative norm nor the exterior coefficient.
No global smoothness assumption on the represented wavefunction is needed.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero

/-- A local equality with a real profile determines the exact norm of its
complex jet. Only the profile needs a local regularity witness. -/
theorem norm_iteratedFDeriv_ofReal_mul_of_eventuallyEq
    {f : Plane → ℝ} {φ : Wavefunction} {Γ : ℝ} {x : Plane} (n : ℕ)
    (hf : ContDiffAt ℝ n f x)
    (heq : φ =ᶠ[𝓝 x] fun y => (Γ * f y : ℂ)) :
    ‖iteratedFDeriv ℝ n φ x‖ = |Γ| * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
  have hscaled : ContDiffAt ℝ n (fun y => Γ * f y) x := contDiffAt_const.mul hf
  have hnorm := Complex.ofRealLI.norm_iteratedFDeriv_comp_left hscaled le_rfl
  change ‖iteratedFDeriv ℝ n (fun y => (Γ * f y : ℂ)) x‖ = _
  rw [show ‖iteratedFDeriv ℝ n (fun y => (Γ * f y : ℂ)) x‖ =
      ‖iteratedFDeriv ℝ n (fun y => Γ * f y) x‖ by
    simpa only [Function.comp_def, Complex.ofRealLI_apply, Complex.ofReal_mul] using hnorm]
  change ‖iteratedFDeriv ℝ n (fun y => Γ • f y) x‖ = _
  rw [iteratedFDeriv_const_smul_apply' hf, norm_smul, Real.norm_eq_abs]

/-- Every jet belongs to the same exact exterior tail. Positivity of the
radius follows from `0 ≤ a < ‖x‖`; the function may be arbitrary inside. -/
theorem norm_iteratedFDeriv_of_exterior_landau_tail
    {b h E a Γ : ℝ} {φ : Wavefunction}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (ha : 0 ≤ a)
    (htail : ∀ y, a < ‖y‖ → φ y = (Γ * landauKernel b h E ‖y‖ : ℂ))
    (n : ℕ) (x : Plane) (hx : a < ‖x‖) :
    ‖iteratedFDeriv ℝ n φ x‖ =
      |Γ| * ‖iteratedFDeriv ℝ n (fun y : Plane => landauKernel b h E ‖y‖) x‖ := by
  have hxpos : 0 < ‖x‖ := ha.trans_lt hx
  have hreal : ContDiffAt ℝ ∞ (fun y : Plane => landauKernel b h E ‖y‖) x :=
    (contDiffAt_landauKernel hb hh hE hxpos).comp x
      (contDiffAt_norm ℝ (norm_pos_iff.mp hxpos))
  apply norm_iteratedFDeriv_ofReal_mul_of_eventuallyEq n (contDiffAt_infty.mp hreal n)
  have hnear : ∀ᶠ y : Plane in 𝓝 x, a < ‖y‖ :=
    (continuous_norm.tendsto x).eventually (Ioi_mem_nhds hx)
  filter_upwards [hnear] with y hy
  exact htail y hy

/-- A common exact-action estimate for all jets through order `n` of the
same exterior wavefunction. Constants and the threshold are fixed before
the energy, semiclassical parameter, coefficient, wavefunction and point. -/
theorem exists_uniform_exterior_landau_jet_bound
    {b Emin Emax a rMin rMax : ℝ} (hb : 0 < b) (hEmin : 0 < Emin)
    (hEmax : Emin ≤ Emax) (ha : 0 ≤ a) (hMin : a < rMin)
    (hMax : rMin ≤ rMax) (n : ℕ) :
    ∃ C > 0, ∃ h₀ > 0, ∀ E ∈ Icc Emin Emax,
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction,
        (∀ y, a < ‖y‖ → φ y = (Γ * landauKernel b h E ‖y‖ : ℂ)) →
        ∀ x : Plane, ‖x‖ ∈ Icc rMin rMax → ∀ j : ℕ, j ≤ n →
          ‖iteratedFDeriv ℝ j φ x‖ ≤
            C * Γ * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E ‖x‖ / h) := by
  obtain ⟨C, hC, h₀, hh₀, hbound⟩ :=
    exists_uniform_landauKernel_spatialJet_bound hb hEmin hEmax (ha.trans_lt hMin) hMax n
  refine ⟨C, hC, h₀, hh₀, ?_⟩
  intro E hE h hh hsmall Γ hΓ φ htail x hx j hj
  rw [norm_iteratedFDeriv_of_exterior_landau_tail hb hh (hEmin.trans_le hE.1)
    ha htail j x (hMin.trans_le hx.1), abs_of_nonneg hΓ]
  calc
    _ ≤ Γ * (C * (h ^ (n + 2))⁻¹ * Real.exp (-bridgeAction b E ‖x‖ / h)) :=
      mul_le_mul_of_nonneg_left (hbound E hE x hx h hh hsmall j hj) hΓ
    _ = _ := by ring

end InfiniteZero
