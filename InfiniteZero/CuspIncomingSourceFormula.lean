import InfiniteZero.AtomicCuspSource
import InfiniteZero.ComplexCuspPhysicalBridge

/-!
# Exact incoming sources in the physical cusp coordinates

Only the radial reference state is replaced by its exact exterior kernel.
The full corrected state is never continued to complex coordinates. These
identities retain the true source factor h⁻², the cusp strength εa and
the same Schur and radial coefficients cΓ.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

theorem coreRadius_lt_norm_cuspChart {p : CuspParameters} (hp : p.BasicConditions)
    {t : ℝ} (ht : 0 < t) (s : ℝ) :
    p.r₀ < ‖p.cuspChart (t, s)‖ := by
  have hn := normalCoordinate_le_norm p (p.cuspChart (t, s))
  rw [normalCoordinate_cuspChart] at hn
  dsimp only [Prod.fst] at hn
  linarith [hp.radius_large, hp.r₀_pos]

/-- The positive cusp's incoming source, including both real cutoffs, is
exactly a scalar coefficient times the actual exterior kernel. -/
theorem incoming_source_plus_cuspChart_eq_kernel
    {p : CuspParameters} (hp : p.BasicConditions) (h E c Γ : ℝ)
    (φ : Wavefunction)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ))
    {t : ℝ} (ht : 0 < t) (s : ℝ) :
    componentSource p h (fun x => (c : ℂ) * φ x) 1 (p.cuspChart (t, s)) =
      (-((h ^ 2)⁻¹ * p.ε * p.a * c * Γ) *
        Real.exp (-p.β * Real.log (p.tStar / t) ^ 2) * p.χa t * p.χb s : ℝ) *
          (landauKernel p.b h E ‖p.cuspChart (t, s)‖ : ℂ) := by
  rw [componentSource_plus_eq]
  dsimp only
  rw [htail _ (coreRadius_lt_norm_cuspChart hp ht s), cuspPlus_cuspChart hp ht]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The lower source uses the reflected real chart and the same radial
coefficient; no reflection hypothesis on an arbitrary full state is used. -/
theorem incoming_source_minus_cuspChart_eq_kernel
    {p : CuspParameters} (hp : p.BasicConditions) (h E c Γ : ℝ)
    (φ : Wavefunction)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ))
    {t : ℝ} (ht : 0 < t) (s : ℝ) :
    componentSource p h (fun x => (c : ℂ) * φ x) 2
        (reflection (p.cuspChart (t, s))) =
      (-((h ^ 2)⁻¹ * p.ε * p.a * c * Γ) *
        Real.exp (-p.β * Real.log (p.tStar / t) ^ 2) * p.χa t * p.χb s : ℝ) *
          (landauKernel p.b h E ‖p.cuspChart (t, s)‖ : ℂ) := by
  rw [componentSource_minus_eq]
  dsimp only
  rw [htail _ (by simpa only [norm_reflection] using
    coreRadius_lt_norm_cuspChart hp ht s), cuspMinus_reflection,
    cuspPlus_cuspChart hp ht, norm_reflection]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- Agreement on real normal coordinates with the already constructed
holomorphic upper kernel. The cutoff and log-flat factors remain explicit. -/
theorem incoming_source_plus_cuspChart_eq_complexKernel
    {p : CuspParameters} (hp : p.BasicConditions) (h E c Γ : ℝ)
    (φ : Wavefunction)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ))
    {t : ℝ} (ht : 0 < t) (s u : ℝ) :
    componentSource p h (fun x => (c : ℂ) * φ x) 1 (p.cuspChart (t, s)) =
      (-((h ^ 2)⁻¹ * p.ε * p.a * c * Γ) *
        Real.exp (-p.β * Real.log (p.tStar / t) ^ 2) * p.χa t * p.χb s : ℝ) *
          Geometry.complexCuspPlusKernel p.b h E p.R s ((t : ℂ), (u : ℂ)) := by
  rw [complexCuspPlusKernel_ofReal]
  exact incoming_source_plus_cuspChart_eq_kernel hp h E c Γ φ htail ht s

theorem incoming_source_minus_cuspChart_eq_complexKernel
    {p : CuspParameters} (hp : p.BasicConditions) (h E c Γ : ℝ)
    (φ : Wavefunction)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ))
    {u : ℝ} (hu : 0 < u) (r t : ℝ) :
    componentSource p h (fun x => (c : ℂ) * φ x) 2
        (reflection (p.cuspChart (u, r))) =
      (-((h ^ 2)⁻¹ * p.ε * p.a * c * Γ) *
        Real.exp (-p.β * Real.log (p.tStar / u) ^ 2) * p.χa u * p.χb r : ℝ) *
          Geometry.complexCuspMinusKernel p.b h E p.R r ((t : ℂ), (u : ℂ)) := by
  rw [complexCuspMinusKernel_ofReal, norm_reflection]
  exact incoming_source_minus_cuspChart_eq_kernel hp h E c Γ φ htail hu r

/-- The exact incoming--incoming integrand on the two real cusp charts.
The two radial kernels have energy Ecore, while the bridge has Efull.
The Jacobians t²u² and the exterior pairing factor -h² are not included
in this pointwise identity. -/
theorem incoming_channelIntegrand_cuspChart_eq
    {p : CuspParameters} (hp : p.BasicConditions) (L h Ecore Efull c Γ : ℝ)
    (φ : Wavefunction)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h Ecore ‖x‖ : ℂ))
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (s r : ℝ) :
    channelIntegrand (sourceKernel p.b L h Efull)
      (componentSource p h (fun x => (c : ℂ) * φ x) 1)
      (componentSource p h (fun x => (c : ℂ) * φ x) 2)
      (p.cuspChart (t, s), reflection (p.cuspChart (u, r))) =
      (((h ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        ((Real.exp (-p.β * Real.log (p.tStar / t) ^ 2) * p.χa t * p.χb s *
          (Real.exp (-p.β * Real.log (p.tStar / u) ^ 2) * p.χa u * p.χb r) : ℝ) : ℂ) *
        (Geometry.complexCuspPlusKernel p.b h Ecore p.R s ((t : ℂ), (u : ℂ)) *
          Geometry.complexCuspMinusKernel p.b h Ecore p.R r ((t : ℂ), (u : ℂ)) *
          Geometry.complexCuspBridgeKernel p.b h Efull p.R L s r ((t : ℂ), (u : ℂ)) *
          Complex.exp (Complex.I * Geometry.complexPhase p.b L
            (Geometry.complexCuspPlus p.R s (t : ℂ))
            (Geometry.complexCuspMinus p.R r (u : ℂ)) / (h : ℂ))) := by
  unfold channelIntegrand
  dsimp only [Prod.fst, Prod.snd]
  rw [incoming_source_plus_cuspChart_eq_kernel hp h Ecore c Γ φ htail ht s,
    incoming_source_minus_cuspChart_eq_kernel hp h Ecore c Γ φ htail hu r,
    sourceKernel_cuspChart_eq, complexCuspPlusKernel_ofReal,
    complexCuspMinusKernel_ofReal, norm_reflection]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  push_cast
  ring

end InfiniteZero.CuspParameters
