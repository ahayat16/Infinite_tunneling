import InfiniteZero.RadialCoreSpectralData
import InfiniteZero.AtomicSpectralCoercivity
import InfiniteZero.AtomicPerturbationSign
import InfiniteZero.SchurGroundCertificate

/-!
# Ground-state construction for the actual core-plus-cusps potential

Radial spectral data are the sole spectral input. The nonradial complement
bound, low trial vector, compression, inverse, scalar root, ground vector,
simplicity and quantitative gap are all consequences proved in Lean.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero.CuspParameters

theorem exists_atomicGroundCertificate_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ E ≤ atomicGroundEnergy p.b p.core coupling,
        ∃ c : GroundStateCertificate (magneticOperator p.b coupling p.potential) E,
          c.gap = hRad.gap / 2 * coupling := by
  obtain ⟨T, hT, hcoer⟩ := exists_atomic_spectral_operator_complement_threshold
    hp hRad.gap_pos hRad.energyBound
  refine ⟨max T hRad.threshold, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcT : T ≤ coupling := (le_max_left _ _).trans hc
  have hcRad : hRad.threshold ≤ coupling := (le_max_right _ _).trans hc
  have hcpos : 0 < coupling := hT.trans_le hcT
  obtain ⟨φ, hφ, hupper, hgap⟩ := hRad.ground coupling hcRad
  let u : L2Space := hφ.1.2.1.toLp φ
  have hu : Represents u φ := represents_toLp hφ.1.2.1
  have huEig : u ∈ operatorEigenspace (magneticOperator p.b coupling p.core)
      (atomicGroundEnergy p.b p.core coupling) :=
    ((hAcore coupling).eigenfunction_iff _ u).mpr ⟨φ, hφ.1, hu⟩
  obtain ⟨v, hv, hvEnergy⟩ := exists_atomicOperator_vector_of_core_eigenvector
    hp coupling (hAcore coupling) (hApot coupling) huEig
  have hunorm : ‖u‖ ^ 2 = 1 := hu.norm_sq_eq_mass.trans hφ.2
  have hvnorm : ‖(v : L2Space)‖ = 1 := by
    rw [hv]
    nlinarith [norm_nonneg u]
  have hdiag : schurDiagonal (magneticOperator p.b coupling p.potential) v ≤
      atomicGroundEnergy p.b p.core coupling := by
    simpa only [schurDiagonal, hunorm, mul_one] using hvEnergy
  have hcancel : coupling ^ 2 * ((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling) =
      atomicGroundEnergy p.b p.core coupling := by field_simp
  have hfull := hcoer coupling hcT (hAcore coupling) (hApot coupling) φ hφ hupper hgap
  refine exists_groundStateCertificate_of_complement_coercive
    (magneticOperator p.b coupling p.potential) (hApot coupling).selfAdjoint
    v hvnorm (mul_pos (div_pos hRad.gap_pos (by norm_num)) hcpos) hdiag ?_
  intro w hw
  have hw' : inner ℂ (hφ.1.2.1.toLp φ) (w : L2Space) = 0 := by
    simpa only [hv] using hw
  simpa only [hcancel] using hfull w hw'

/-- Existence, simplicity and isolation for the constructed potential, with
only the radial spectral contract and general realization supplied. -/
theorem eventual_atomicGround_properties_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      AtomicGroundSimple p.b p.potential coupling ∧
      HasGapAboveGround (magneticOperator p.b coupling p.potential)
        (atomicGroundEnergy p.b p.potential coupling) ∧
      atomicGroundEnergy p.b p.potential coupling ≤ atomicGroundEnergy p.b p.core coupling := by
  obtain ⟨T, hT, hcert⟩ := exists_atomicGroundCertificate_of_radialData hp hRad hAcore hApot
  refine ⟨T, hT, ?_⟩
  intro coupling hc
  obtain ⟨E, hE, c, _⟩ := hcert coupling hc
  obtain ⟨hex, hs, hgap⟩ := (hApot coupling).atomicGround_properties_of_certificate c
  exact ⟨hex, hs, hgap, ((hApot coupling).atomicGroundEnergy_eq_of_certificate c).trans_le hE⟩

end InfiniteZero.CuspParameters
