import InfiniteZero.AtomicComponentSourceL1
import InfiniteZero.RadialCoreCoefficientUniqueness
import InfiniteZero.SourcePhaseInvariance
import InfiniteZero.AtomicGroundConstruction

/-!
# Universal component-source L¹ bounds for supplied ground states

The positive radial reference and its exterior coefficient are fixed by
uniqueness. Every full normalized atomic ground state differs from the
existing source witness only by a unit phase, which preserves each source
L¹ norm. The constants precede all states and coefficients supplied later.
-/

noncomputable section
open Set MeasureTheory
namespace InfiniteZero

/-- Exact phase-independent L¹ norms for two true full atomic ground states. -/
theorem AtomicGroundSimple.integral_norm_componentSource_eq
    {p : CuspParameters} {coupling h : ℝ}
    (hsimple : AtomicGroundSimple p.b p.potential coupling)
    {ψ₀ ψ : Wavefunction}
    (hψ₀ : IsAtomicGroundState p.b p.potential coupling ψ₀)
    (hψ : IsAtomicGroundState p.b p.potential coupling ψ) (i : Fin 3) :
    (∫ x : Plane, ‖componentSource p h ψ i x‖) =
      ∫ x : Plane, ‖componentSource p h ψ₀ i x‖ := by
  obtain ⟨z, hz, hphase⟩ := hsimple ψ₀ ψ hψ₀ hψ
  rw [hphase]
  exact integral_norm_componentSource_smul_unit p h z hz ψ₀ i

namespace CuspParameters

/-- The same bound applies to every supplied positive core reference, its own
exact tail coefficient, and every normalized full ground state. -/
theorem exists_universal_component_source_L1_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) :
    ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ → IsPositiveRadial φ →
      ∀ Γ : ℝ,
        (∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel p.b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) →
      ∀ ψ : Wavefunction, IsAtomicGroundState p.b p.potential coupling ψ →
        (∀ i : Fin 3, Integrable (componentSource p coupling⁻¹ ψ i)) ∧
        ((∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 0 x‖) ≤
          coreSourceConstant p * coupling ^ 2) ∧
        ((∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 1 x‖) +
          (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 2 x‖) ≤
            C * Γ * coupling ^ 6 * Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
              Real.exp (-β₁ * (Real.log coupling) ^ 2)) := by
  obtain ⟨C, hC, Ts, hTs, hsource⟩ :=
    exists_atomicGround_component_source_L1_of_radialData
      hInterior hp hRad hAcore hApot χ hβ₁ hβ₁β
  obtain ⟨Tg, _hTg, hground⟩ :=
    eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  refine ⟨C, hC, max Ts (max hRad.threshold Tg), hTs.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc φ hφ hφpos Γ htail ψ hψ
  have hcs : Ts ≤ coupling := (le_max_left _ _).trans hc
  have hcr : hRad.threshold ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans hc)
  have hcg : Tg ≤ coupling := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  obtain ⟨φ₀, ψ₀, hφ₀, hφ₀pos, hψ₀, _c, _hc, Γ₀, _hΓ₀, htail₀,
    _hIntegrable, hcore, hcusps⟩ := hsource coupling hcs
  have hΓeq := (hRad.positive_ground_coefficient_unique hp.r₀_pos (hAcore coupling)
    hcr hφ₀ hφ₀pos hφ hφpos htail₀ htail).2
  subst Γ₀
  have hsimple := (hground coupling hcg).2.1
  have hnorm (i : Fin 3) :=
    hsimple.integral_norm_componentSource_eq (h := coupling⁻¹) hψ₀ hψ i
  refine ⟨fun i => componentSource_integrable hp coupling⁻¹ hψ.1.1.continuous i, ?_, ?_⟩
  · rw [hnorm 0]
    exact hcore
  · rw [hnorm 1, hnorm 2]
    exact hcusps

end CuspParameters
end InfiniteZero
