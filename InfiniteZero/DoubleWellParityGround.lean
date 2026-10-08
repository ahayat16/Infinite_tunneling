import InfiniteZero.ParitySchurGroundConstruction
import InfiniteZero.ParityTrialCoercivity
import InfiniteZero.ParityTrialEnergyBound

/-!
# Construction of the two genuine parity ground states

The actual normalized atomic trials have energy at most `Eatom + γλ/8`.
Their sector complements have energy at least `Eatom + γλ/4`. The genuine
reducing restrictions and the Schur theorem therefore construct each
parity ground state, identify its energy with `parityEnergy`, and retain
the absolute floor `Eatom + γλ/4` on its sector complement.

All estimates are proved for the constructed potential. The explicit
inputs are only the classical radial data and operator realizations.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem exists_doubleWell_parityGroundCertificates_of_radialData
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
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ even : Bool, ∃ c : ParityGroundCertificate
        (magneticOperator p.b coupling (doubleWellPotential p.potential L)) even
        (parityEnergy p.b p.potential L coupling even),
        parityEnergy p.b p.potential L coupling even ≤
          atomicGroundEnergy p.b p.potential coupling + hRad.gap / 8 * coupling ∧
        hRad.gap / 8 * coupling ≤ c.gap ∧
        parityEnergy p.b p.potential L coupling even + c.gap =
          atomicGroundEnergy p.b p.potential coupling + hRad.gap / 4 * coupling := by
  obtain ⟨Tg, hTg, hgap⟩ := exists_parityTrial_complement_gap_of_radialData
    hp cert hRad hAcore hApot hAdouble
  obtain ⟨Te, _, htrial⟩ := exists_parityTrial_energy_upper_of_radialData
    hp cert hRad hAcore hApot
  refine ⟨max Tg Te, hTg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL even
  have hcg := (le_max_left Tg Te).trans hc
  have hce := (le_max_right Tg Te).trans hc
  have hcpos := hTg.trans_le hcg
  obtain ⟨φ, hφ⟩ := (hgap coupling hcg).1
  obtain ⟨q, hq, hqn, hqp, _, hqe⟩ := htrial coupling hce L hL φ hφ
    (hAleft coupling L) (hAright coupling L) (hAdouble coupling L) even
  have hg : 0 < hRad.gap / 8 * coupling :=
    mul_pos (div_pos hRad.gap_pos (by norm_num)) hcpos
  have hbound : ∀ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
      HasL2Parity even (u : L2Space) → inner ℂ (q : L2Space) (u : L2Space) = 0 →
      (atomicGroundEnergy p.b p.potential coupling + hRad.gap / 8 * coupling +
        hRad.gap / 8 * coupling) * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator p.b coupling (doubleWellPotential p.potential L) u)).re := by
    intro u hu horth
    have h := (hgap coupling hcg).2 L hL φ hφ even (q : L2Space) hq u hu horth
    convert h using 1
    ring
  obtain ⟨E, hE, c, hcgap, hcle⟩ := exists_parityGroundCertificate_of_complement_coercive
    (magneticOperator p.b coupling (doubleWellPotential p.potential L))
    (hAdouble coupling L).selfAdjoint even
    ((hAdouble coupling L).parityStarProjection_double_graph even) q hqn hqp hg hqe hbound
  have hV : Continuous (doubleWellPotential p.potential L) :=
    ((potential_contDiff hp).continuous.comp (continuous_id.add continuous_const)).add
      ((potential_contDiff hp).continuous.comp (continuous_id.neg.add continuous_const))
  have hid := c.parityEnergy_eq (hAdouble coupling L) hV
  rw [hid]
  refine ⟨c, hE, hcle, ?_⟩
  rw [hcgap]
  ring

end InfiniteZero.CuspParameters
