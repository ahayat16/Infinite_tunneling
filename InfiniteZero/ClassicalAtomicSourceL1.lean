import InfiniteZero.Remaining
import InfiniteZero.ClassicalEllipticInterior
import InfiniteZero.AtomicSourceL1

/-!
# Classical wrapper for the genuine cusp source L¹ estimates

The same atomic states and exterior radial coefficient give both incoming
and scattered cusp source bounds. The incoming logarithmic margin and the
sum of the two scattered margins remain distinct. The auxiliary cutoff is
chosen only within the proof. The classical inputs are A002, A004 and A005.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- Fine L¹ estimates of the actual incoming and scattered cusp components,
with one common choice of normalized atomic states and exterior coefficient. -/
theorem atomicGround_source_L1
    {p : CuspParameters} (hp : p.BasicConditions) {βin βglobal βlocal : ℝ}
    (hi : 0 < βin) (hiβ : βin < p.β)
    (hg : 0 < βglobal) (hgβ : βglobal < p.β)
    (hl : 0 < βlocal) (hlβ : βlocal < p.β) :
    ∃ Cin > 0, ∃ Csc > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let G : ℝ := c * Γ * Real.exp (-coupling * bridgeAction p.b
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          ∀ i : Fin 3, i = 1 ∨ i = 2 →
            Integrable (componentSource p coupling⁻¹ (fun y => (c : ℂ) * φ y) i) ∧
            Integrable (componentSource p coupling⁻¹ η i) ∧
            (∫ x : Plane, ‖componentSource p coupling⁻¹ (fun y => (c : ℂ) * φ y) i x‖) ≤
              Cin * coupling ^ 4 * G * Real.exp (-βin * (Real.log coupling) ^ 2) ∧
            (∫ x : Plane, ‖componentSource p coupling⁻¹ η i x‖) ≤
              Csc * coupling ^ 6 * G *
                Real.exp (-(βglobal + βlocal) * (Real.log coupling) ^ 2) := by
  let χ := Classical.choice (exists_cuspWeightCutoffs hp)
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  have hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core := by
    intro coupling
    apply magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential := by
    intro coupling
    exact magnetic_realization p.b coupling p.potential
      (admissiblePotential hp).smooth (admissiblePotential hp).bounded
  exact exists_atomicGround_source_L1_of_radialData
    classical_elliptic_interior_estimate hp hRad hAcore hApot χ hi hiβ hg hgβ hl hlβ

end InfiniteZero.CuspParameters
