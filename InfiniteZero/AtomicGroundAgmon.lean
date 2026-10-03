import InfiniteZero.AtomicAgmonGlobal
import InfiniteZero.AtomicGroundEnergyBounds

/-!
# Exterior decay of the constructed atomic ground states

The radial spectral data and the two operator realizations supply the actual
ground state and its low-energy regime. A single pair of Agmon constants then
controls every normalized ground state of either the full potential or its
radial core. The final corollary applies directly to the canonical full state.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero.CuspParameters

/-- Common exterior decay constants for the full and radial atomic ground
states. The energy restrictions needed by the global Agmon estimate are
deduced from the radial data, rather than assumed of the states. -/
theorem exists_atomicGround_agmon_tail_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      (∀ φ, IsAtomicGroundState p.b p.potential coupling φ →
        (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
          (C / coupling ^ 2) * Real.exp (-2 * d * coupling)) ∧
      (∀ φ, IsAtomicGroundState p.b p.core coupling φ →
        (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
          (C / coupling ^ 2) * Real.exp (-2 * d * coupling)) := by
  obtain ⟨C, hC, d, hd, htail⟩ := exists_atomicAgmon_tail_bound p hp.r₀_pos
  obtain ⟨Tg, hTg, hground⟩ :=
    eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  obtain ⟨Te, _, henergy⟩ :=
    exists_atomicGroundEnergy_bounds_of_radialData hp hRad hAcore hApot
  let T := max Tg (max Te (max hRad.threshold (4 * hRad.energyBound)))
  refine ⟨C, hC, d, hd, T, hTg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcg : Tg ≤ coupling := (le_max_left _ _).trans hc
  have hcrest : max Te (max hRad.threshold (4 * hRad.energyBound)) ≤ coupling :=
    (le_max_right _ _).trans hc
  have hce : Te ≤ coupling := (le_max_left _ _).trans hcrest
  have hcrest' : max hRad.threshold (4 * hRad.energyBound) ≤ coupling :=
    (le_max_right _ _).trans hcrest
  have hcRad : hRad.threshold ≤ coupling := (le_max_left _ _).trans hcrest'
  have hcB : 4 * hRad.energyBound ≤ coupling := (le_max_right _ _).trans hcrest'
  have hcpos : 0 < coupling := hTg.trans_le hcg
  have hlinear : hRad.energyBound * coupling ≤ coupling ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right hcB hcpos.le
    nlinarith only [h]
  have hEfull : atomicGroundEnergy p.b p.potential coupling ≤
      -(3 / 4 : ℝ) * coupling ^ 2 := by
    have h := (henergy coupling hce).2
    linarith only [h, hlinear]
  have hEcore : atomicGroundEnergy p.b p.core coupling ≤
      -(3 / 4 : ℝ) * coupling ^ 2 := by
    obtain ⟨φ, _, hupper, _⟩ := hRad.ground coupling hcRad
    have hscaled := mul_le_mul_of_nonneg_left hupper (sq_nonneg coupling)
    have hcancel : coupling ^ 2 * ((coupling⁻¹) ^ 2 *
        atomicGroundEnergy p.b p.core coupling) =
        atomicGroundEnergy p.b p.core coupling := by field_simp
    have hright : coupling ^ 2 * (-1 + hRad.energyBound / coupling) =
        -coupling ^ 2 + hRad.energyBound * coupling := by field_simp
    change coupling ^ 2 * ((coupling⁻¹) ^ 2 *
        atomicGroundEnergy p.b p.core coupling) ≤
        coupling ^ 2 * (-1 + hRad.energyBound / coupling) at hscaled
    rw [hcancel, hright] at hscaled
    linarith only [hscaled, hlinear]
  refine ⟨(hground coupling hcg).1, ?_, ?_⟩
  · intro φ hφ
    exact htail p.b coupling _ p.potential φ hcpos (potential_contDiff hp).continuous
      hφ.1 hφ.2 (fun x hx => potential_exterior_spectral_reserve hp hEfull hx)
  · intro φ hφ
    apply htail p.b coupling _ p.core φ hcpos (core_contDiff hp.r₀_pos).continuous hφ.1 hφ.2
    intro x hx
    have hz : p.core x = 0 := by simp [core, not_lt.mpr hx]
    rw [hz, mul_zero, zero_sub]
    nlinarith only [hEcore, sq_nonneg coupling]

/-- The canonical atomic state is a genuine normalized ground state and has
exponentially small mass outside `4 r₀`, with no additional state or energy
assumption. -/
theorem exists_canonicalAtomicState_agmon_tail_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsAtomicGroundState p.b p.potential coupling
        (canonicalAtomicState p.b p.potential coupling) ∧
      (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖},
        ‖canonicalAtomicState p.b p.potential coupling x‖ ^ 2) ≤
        (C / coupling ^ 2) * Real.exp (-2 * d * coupling) := by
  obtain ⟨C, hC, d, hd, T, hT, hbound⟩ :=
    exists_atomicGround_agmon_tail_of_radialData hp hRad hAcore hApot
  refine ⟨C, hC, d, hd, T, hT, ?_⟩
  intro coupling hc
  obtain ⟨hexists, hfull, _⟩ := hbound coupling hc
  have hφ := canonicalAtomicState_spec p.b p.potential coupling hexists
  exact ⟨hφ, hfull _ hφ⟩

end InfiniteZero.CuspParameters
