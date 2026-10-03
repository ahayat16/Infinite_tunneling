import InfiniteZero.ParityEnergyContinuity
import InfiniteZero.ParityTrialEnergyBound
import InfiniteZero.MagneticParityNormalization

/-!
# Continuity of parity energies for the constructed potential

A single sufficiently large auxiliary coupling supplies a normalized
parity-domain vector. The actual parity test core is then nonempty, and
its nonemptiness is independent of the coupling parameter. Global dilation
therefore gives continuity at every positive coupling. All radial and
operator-realization inputs remain explicit.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

/-- The actual two-well trial vector makes each normalized parity test set nonempty. -/
theorem exists_normalized_parity_test_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∀ L : ℝ, cert.L₀ ≤ L → ∀ even : Bool,
      ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ := by
  obtain ⟨_, _, _, _, Ta, _, hground⟩ :=
    exists_atomicGround_agmon_tail_of_radialData hp hRad hAcore hApot
  obtain ⟨Tt, _, htrial⟩ :=
    exists_parityTrial_energy_upper_of_radialData hp cert hRad hAcore hApot
  let coupling := max Ta Tt
  obtain ⟨φ, hφ⟩ := (hground coupling (le_max_left _ _)).1
  intro L hL even
  obtain ⟨u, _, hn, hpar, _, _⟩ := htrial coupling (le_max_right _ _) L hL φ hφ
    (hAleft coupling L) (hAright coupling L) (hAdouble coupling L) even
  have hV : Continuous (doubleWellPotential p.potential L) :=
    ((potential_contDiff hp).continuous.comp (continuous_id.add continuous_const)).add
      ((potential_contDiff hp).continuous.comp (continuous_id.neg.add continuous_const))
  have hu0 : (u : L2Space) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  exact (hAdouble coupling L).exists_normalized_parity_test_of_domain_vector hV even u hpar hu0

/-- Continuity holds on the entire positive half-line after eliminating test nonemptiness. -/
theorem continuousOn_parityEnergy_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∀ L : ℝ, cert.L₀ ≤ L → ∀ even : Bool,
      ContinuousOn (fun coupling : ℝ => parityEnergy p.b p.potential L coupling even) (Ioi 0) := by
  intro L hL even
  apply continuousOn_parityEnergy p.b L even (potential_contDiff hp)
    (potential_hasCompactSupport hp)
  exact exists_normalized_parity_test_of_radialData
    hp cert hRad hAcore hApot hAleft hAright hAdouble L hL even

/-- The concrete odd-minus-even variational splitting is continuous at positive coupling. -/
theorem continuousOn_signedSplitting_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∀ L : ℝ, cert.L₀ ≤ L → ContinuousOn (signedSplitting p.b p.potential L) (Ioi 0) := by
  intro L hL
  have h := continuousOn_parityEnergy_of_radialData
    hp cert hRad hAcore hApot hAleft hAright hAdouble L hL
  exact (h false).sub (h true)

end InfiniteZero.CuspParameters
