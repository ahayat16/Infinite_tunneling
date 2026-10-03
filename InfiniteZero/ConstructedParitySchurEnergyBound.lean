import InfiniteZero.ParitySchurEnergyShift
import InfiniteZero.ParityTrialCoercivity
import InfiniteZero.ParityTrialEnergyBound
import InfiniteZero.ParityTrialRayleigh

/-!
# Quantitative Schur energy correction for the constructed double well

The coarse physical estimates provide one common threshold, before the
well separation, the atomic-state phase, and the parity. Every domain
representative of the actual normalized trial then has the same quadratic
energy-shift bound. Sharp opposite-support estimates can be inserted into
its right-hand side without reconstructing the spectral modes.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem exists_parityTrial_energy_shift_bounds_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ (_hAleft : IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
        (_hAright : IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
        (even : Bool)
        (u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain),
        Represents (u : L2Space) (normalizedParityTrialState even p.b L coupling φ) →
        0 ≤ schurDiagonal (magneticOperator p.b coupling (doubleWellPotential p.potential L)) u -
            parityEnergy p.b p.potential L coupling even ∧
          schurDiagonal (magneticOperator p.b coupling (doubleWellPotential p.potential L)) u -
            parityEnergy p.b p.potential L coupling even ≤
            ‖magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
              (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space)‖ ^ 2 /
              (hRad.gap / 8 * coupling) := by
  obtain ⟨Tg, hTg, hgap⟩ := exists_parityTrial_complement_gap_of_radialData
    hp cert hRad hAcore hApot hAdouble
  obtain ⟨Te, _, htrial⟩ := exists_parityTrial_energy_upper_of_radialData
    hp cert hRad hAcore hApot
  refine ⟨max Tg Te, hTg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL φ hφ hAleft hAright even u hu
  have hcg := (le_max_left Tg Te).trans hc
  have hce := (le_max_right Tg Te).trans hc
  have hcpos := hTg.trans_le hcg
  obtain ⟨q, hq, hqn, hqp, _, hqe⟩ := htrial coupling hce L hL φ hφ
    hAleft hAright (hAdouble coupling L) even
  have huq : u = q := Subtype.ext (MeasureTheory.Lp.ext (hu.trans hq.symm))
  subst u
  have hg : 0 < hRad.gap / 8 * coupling :=
    mul_pos (div_pos hRad.gap_pos (by norm_num)) hcpos
  have hbound : ∀ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
      HasL2Parity even (u : L2Space) → inner ℂ (q : L2Space) (u : L2Space) = 0 →
      (atomicGroundEnergy p.b p.potential coupling + hRad.gap / 8 * coupling +
        hRad.gap / 8 * coupling) * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator p.b coupling (doubleWellPotential p.potential L) u)).re := by
    intro u hp horth
    have h := (hgap coupling hcg).2 L hL φ hφ even (q : L2Space) hq u hp horth
    convert h using 1
    ring
  have hV : Continuous (doubleWellPotential p.potential L) :=
    ((potential_contDiff hp).continuous.comp (continuous_id.add continuous_const)).add
      ((potential_contDiff hp).continuous.comp (continuous_id.neg.add continuous_const))
  exact (hAdouble coupling L).parityEnergy_shift_bounds_of_complement_coercive
    hV even q hqn hqp hg hqe hbound (atomicGroundEnergy p.b p.potential coupling)

end InfiniteZero.CuspParameters
