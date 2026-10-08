import InfiniteZero.AtomicGroundConstruction
import InfiniteZero.SchurResidualBounds

/-!
# Constructing quantitative Schur reference data for the actual potential

The reference is an actual radial ground state in the full operator domain.
The data retain its representative, the full complement lower bound, and the
residual estimates. Their existence is proved from the radial spectral data
and the two general operator realizations, without a nonradial spectral input.
-/

noncomputable section
namespace InfiniteZero

structure AtomicSchurReference (p : CuspParameters) (hp : p.BasicConditions)
    (coupling gap : ℝ) where
  coreState : Wavefunction
  coreGround : IsAtomicGroundState p.b p.core coupling coreState
  vector : (magneticOperator p.b coupling p.potential).domain
  represents : Represents (vector : L2Space) coreState
  diagonal_le : schurDiagonal (magneticOperator p.b coupling p.potential) vector ≤
    atomicGroundEnergy p.b p.core coupling
  coupling_le : ‖schurCoupling (magneticOperator p.b coupling p.potential) vector‖ ≤
    ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp (vector : L2Space)‖
  diagonal_error_le :
    |schurDiagonal (magneticOperator p.b coupling p.potential) vector -
      atomicGroundEnergy p.b p.core coupling| ≤
    ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp (vector : L2Space)‖
  complement_lower : ∀ u : (magneticOperator p.b coupling p.potential).domain,
    inner ℂ (vector : L2Space) (u : L2Space) = 0 →
    (atomicGroundEnergy p.b p.core coupling + gap) * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (magneticOperator p.b coupling p.potential u)).re

theorem AtomicSchurReference.vector_norm {p : CuspParameters} {hp : p.BasicConditions}
    {coupling gap : ℝ} (h : AtomicSchurReference p hp coupling gap) :
    ‖(h.vector : L2Space)‖ = 1 := by
  have hs := h.represents.norm_sq_eq_mass.trans h.coreGround.2
  nlinarith [norm_nonneg (h.vector : L2Space)]

namespace CuspParameters

/-- These reference data are constructed at one threshold independent of the
coupling. The full-potential complement bound is proved, not supplied. -/
theorem exists_atomicSchurReference_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      Nonempty (AtomicSchurReference p hp coupling (hRad.gap / 2 * coupling)) := by
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
  have hunorm : ‖u‖ = 1 := by
    have hs := hu.norm_sq_eq_mass.trans hφ.2
    nlinarith [norm_nonneg u]
  obtain ⟨v, hv, hB, hdiagError⟩ := exists_atomic_schur_reference_of_core_eigenvector
    hp coupling (hAcore coupling) (hApot coupling) huEig hunorm
  obtain ⟨w, hw, hwEnergy⟩ := exists_atomicOperator_vector_of_core_eigenvector
    hp coupling (hAcore coupling) (hApot coupling) huEig
  have hwv : w = v := Subtype.ext (hw.trans hv.symm)
  have hdiag : schurDiagonal (magneticOperator p.b coupling p.potential) v ≤
      atomicGroundEnergy p.b p.core coupling := by
    simpa only [hwv, hunorm, one_pow, mul_one, schurDiagonal] using hwEnergy
  have hcancel : coupling ^ 2 * ((coupling⁻¹) ^ 2 *
      atomicGroundEnergy p.b p.core coupling) =
      atomicGroundEnergy p.b p.core coupling := by field_simp
  have hfull := hcoer coupling hcT (hAcore coupling) (hApot coupling) φ hφ hupper hgap
  refine ⟨⟨φ, hφ, v, ?_, hdiag, ?_, ?_, ?_⟩⟩
  · simpa only [hv] using hu
  · simpa only [hv] using hB
  · simpa only [hv] using hdiagError
  · intro z hz
    have hz' : inner ℂ (hφ.1.2.1.toLp φ) (z : L2Space) = 0 := by
      simpa only [hv] using hz
    simpa only [hcancel] using hfull z hz'

end CuspParameters
end InfiniteZero
