import InfiniteZero.ConstructedParitySchurEnergyBound
import InfiniteZero.CanonicalOverlapDecay

/-!
# Canonical physical parity corrections

The correction is the exact physical Rayleigh quotient minus the actual
sector ground energy. Its definition makes no spectral assertion. For the
constructed potential, the proved Schur estimate gives its nonnegativity
and its quadratic residual bound at one common coupling threshold.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace InfiniteZero

def canonicalParityCorrection (b : ℝ) (v : Potential) (L coupling : ℝ)
    (even : Bool) : ℝ :=
  atomicGroundEnergy b v coupling +
    (canonicalDefect b v L coupling +
      if even then (canonicalHopping b v L coupling).re else
        -(canonicalHopping b v L coupling).re) /
    (1 + if even then canonicalOverlap b v L coupling else
      -canonicalOverlap b v L coupling) - parityEnergy b v L coupling even

theorem evenEnergy_eq_canonicalParityCorrection (b : ℝ) (v : Potential)
    (L coupling : ℝ) :
    evenEnergy b v L coupling = atomicGroundEnergy b v coupling +
      (canonicalDefect b v L coupling + (canonicalHopping b v L coupling).re) /
        (1 + canonicalOverlap b v L coupling) -
      canonicalParityCorrection b v L coupling true := by
  simp only [canonicalParityCorrection, evenEnergy, ↓reduceIte]
  ring

theorem oddEnergy_eq_canonicalParityCorrection (b : ℝ) (v : Potential)
    (L coupling : ℝ) :
    oddEnergy b v L coupling = atomicGroundEnergy b v coupling +
      (canonicalDefect b v L coupling - (canonicalHopping b v L coupling).re) /
        (1 - canonicalOverlap b v L coupling) -
      canonicalParityCorrection b v L coupling false := by
  simp only [canonicalParityCorrection, oddEnergy, Bool.false_eq_true, ↓reduceIte,
    sub_eq_add_neg]
  ring

theorem canonicalParityCorrection_eq_schurDiagonal_sub
    {b coupling L : ℝ} {v : Potential}
    (hExists : ∃ φ, IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) (hs : |canonicalOverlap b v L coupling| < 1)
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : Represents (u : L2Space)
      (normalizedParityTrialState even b L coupling (canonicalAtomicState b v coupling))) :
    canonicalParityCorrection b v L coupling even =
      schurDiagonal (magneticOperator b coupling (doubleWellPotential v L)) u -
        parityEnergy b v L coupling even := by
  rw [canonicalParityTrial_schurDiagonal hExists hv hbound hAleft hAright hAdouble even hs u hu]
  rfl

/-- Once the physical error estimates are known, the exact transfer package
uses the fixed corrections, with no choice of a new spectral witness. -/
def canonicalParitySchurDataOfSmallErrors
    {b L : ℝ} {v : Potential} {A : ℝ → ℝ}
    (hs : Tendsto (canonicalOverlap b v L) atTop (𝓝 0))
    (hδ : Asymptotics.IsLittleO atTop (canonicalDefect b v L) A)
    (hσ : ∀ even : Bool,
      Asymptotics.IsLittleO atTop (fun coupling => canonicalParityCorrection b v L coupling even) A) :
    CanonicalParitySchurData b v L A where
  threshold := 0
  sigmaEven := fun coupling => canonicalParityCorrection b v L coupling true
  sigmaOdd := fun coupling => canonicalParityCorrection b v L coupling false
  even_equation := fun coupling _ => evenEnergy_eq_canonicalParityCorrection b v L coupling
  odd_equation := fun coupling _ => oddEnergy_eq_canonicalParityCorrection b v L coupling
  overlap_tendsto := hs
  defect_small := hδ
  sigmaEven_small := hσ true
  sigmaOdd_small := hσ false

namespace CuspParameters

theorem exists_canonicalParityCorrection_residual_bounds_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ (_hAleft : IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
        (_hAright : IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
        (even : Bool)
        (u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain),
        Represents (u : L2Space) (normalizedParityTrialState even p.b L coupling
          (canonicalAtomicState p.b p.potential coupling)) →
        0 ≤ canonicalParityCorrection p.b p.potential L coupling even ∧
          canonicalParityCorrection p.b p.potential L coupling even ≤
            ‖magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
              (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space)‖ ^ 2 /
              (hRad.gap / 8 * coupling) := by
  obtain ⟨Tg, hTg, hshift⟩ := exists_parityTrial_energy_shift_bounds_of_radialData
    hp cert hRad hAcore hApot hAdouble
  obtain ⟨Ta, _, hatom⟩ := eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  obtain ⟨Ts, _, hsmall⟩ := exists_canonicalOverlap_uniform_small_of_radialData
    hp hRad hAcore hApot (by norm_num : (0 : ℝ) < 1)
  refine ⟨max Tg (max Ta Ts), hTg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL hAleft hAright even u hu
  have hcg : Tg ≤ coupling := (le_max_left _ _).trans hc
  have hca : Ta ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcs : Ts ≤ coupling := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hExists := (hatom coupling hca).1
  have hφ := canonicalAtomicState_spec p.b p.potential coupling hExists
  have hfour : 4 * p.r₀ ≤ L := by
    have hR : p.R < L := ((le_max_right _ _).trans_lt cert.separation).trans_le hL
    linarith [hp.radius_large, hp.r₀_pos]
  have hbound : ∀ x, |p.potential x| ≤ 1 := by
    intro x
    obtain ⟨hl, hr⟩ := potential_range hp x
    exact abs_le.mpr ⟨hl, hr.trans (by norm_num)⟩
  rw [canonicalParityCorrection_eq_schurDiagonal_sub hExists
    (potential_contDiff hp).continuous hbound hAleft hAright (hAdouble coupling L)
    even (hsmall coupling hcs L hfour) u hu]
  exact hshift coupling hcg L hL _ hφ hAleft hAright even u hu

end CuspParameters
end InfiniteZero
