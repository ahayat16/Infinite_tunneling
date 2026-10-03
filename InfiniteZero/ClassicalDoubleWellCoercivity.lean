import InfiniteZero.Remaining
import InfiniteZero.DoubleWellOperatorCoercivity

/-!
# Coercivity on the physical two-well complement

The only classical inputs instantiated here are A002 and A004. The gap of
the full atom, the fixed three-piece localization, its overlap errors and
the transfer from tests to the closed graph are proved in the conditional
modules. This conclusion concerns the complement of the two translated
atomic states, not the spectral decomposition into parity eigenmodes.
-/

noncomputable section

namespace InfiniteZero.CuspParameters

/-- One positive gap coefficient and one coupling threshold work for every
later separation and every normalized atomic ground state. The references
are arbitrary L² representatives of that same state's left and right modes. -/
theorem doubleWell_complement_coercivity {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ γ > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ vL vR : L2Space, Represents vL (leftState p.b L coupling φ) →
        Represents vR (rightState p.b L coupling φ) →
      ∀ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
        inner ℂ vL (u : L2Space) = 0 → inner ℂ vR (u : L2Space) = 0 →
        (atomicGroundEnergy p.b p.potential coupling + γ * coupling) *
          ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator p.b coupling (doubleWellPotential p.potential L) u)).re := by
  let hRad := Classical.choice (radial_core_spectral_data p.b p hp.b_pos hp.r₀_pos)
  refine ⟨hRad.gap / 4, div_pos hRad.gap_pos (by norm_num), ?_⟩
  apply exists_doubleWell_operator_complement_gap_of_radialData hp cert hRad
  · intro coupling
    apply magnetic_realization p.b coupling p.core (core_contDiff hp.r₀_pos)
    refine ⟨1, fun x => ?_⟩
    have hx := core_range p x
    rw [abs_le]
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  · intro coupling
    exact magnetic_realization p.b coupling p.potential
      (admissiblePotential hp).smooth (admissiblePotential hp).bounded
  · intro coupling L
    exact magnetic_realization p.b coupling (doubleWellPotential p.potential L)
      ((admissiblePotential hp).doubleWell_smooth L)
      ((admissiblePotential hp).doubleWell_bounded L)

end InfiniteZero.CuspParameters
