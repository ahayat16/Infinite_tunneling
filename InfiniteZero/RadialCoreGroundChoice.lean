import InfiniteZero.RadialCoreSpectralData
import InfiniteZero.ConstructionCoreSmooth
import InfiniteZero.MagneticGraphLowerBound
import InfiniteZero.GroundStateCertificate

/-!
# A positive radial reference carrying the original spectral gap

The two ground-state witnesses in `RadialCoreSpectralData` need not have
been chosen together. The test-function gap extends to the actual closed
operator graph and implies simplicity. Consequently any normalized ground
state, in particular the positive radial choice, carries exactly the same
rank-one test estimate. No additional spectral input is used.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

/-- A unit scalar in the first entry does not change the overlap norm. -/
theorem norm_waveInner_smul_unit (φ u : Wavefunction) {c : ℂ} (hc : ‖c‖ = 1) :
    ‖waveInner (c • φ) u‖ = ‖waveInner φ u‖ := by
  have hinner : waveInner (c • φ) u = star c * waveInner φ u := by
    simp only [waveInner, Pi.smul_apply, smul_eq_mul, star_mul']
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  rw [hinner, norm_mul, norm_star, hc, one_mul]

namespace RadialCoreSpectralData

/-- The radial test gap already implies simplicity of the actual core ground
space, using the specified closed-graph realization. -/
theorem core_groundSimple {b : ℝ} {p : CuspParameters}
    (hRad : RadialCoreSpectralData b p) (hr : 0 < p.r₀) {coupling : ℝ}
    (hAcore : IsMagneticRealization b coupling p.core)
    (hT : hRad.threshold ≤ coupling) :
    AtomicGroundSimple b p.core coupling := by
  have hc : 0 < coupling := hRad.threshold_pos.trans_le hT
  obtain ⟨φ, hφ, _, hgap⟩ := hRad.ground coupling hT
  have hcancel : coupling ^ 2 * ((coupling⁻¹) ^ 2 *
      atomicGroundEnergy b p.core coupling) = atomicGroundEnergy b p.core coupling := by
    field_simp
  have hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      (hRad.gap * coupling) * mass ψ -
        (hRad.gap * coupling) * ‖waveInner φ ψ‖ ^ 2 ≤
      magneticForm b coupling p.core ψ -
        atomicGroundEnergy b p.core coupling * mass ψ := by
    intro ψ hψ
    simpa only [mul_sub, hcancel] using hgap ψ hψ
  let u : L2Space := hφ.1.2.1.toLp φ
  have hu : Represents u φ := represents_toLp hφ.1.2.1
  have huG : u ∈ operatorEigenspace (magneticOperator b coupling p.core)
      (atomicGroundEnergy b p.core coupling) :=
    (hAcore.eigenfunction_iff _ u).mpr ⟨φ, hφ.1, hu⟩
  obtain ⟨v, hv, hvA⟩ := (magneticOperator b coupling p.core).mem_graph_iff.mp
    ((mem_operatorEigenspace _ _ _).mp huG)
  let cert : GroundStateCertificate (magneticOperator b coupling p.core)
      (atomicGroundEnergy b p.core coupling) := {
    vector := v
    vector_ne_zero := by simpa only [hv] using hu.ne_zero_of_mass_one hφ.2
    eigenvector := by simpa only [hv] using hvA
    lower_bound := hAcore.lower_bound
    gap := hRad.gap * coupling
    gap_pos := mul_pos hRad.gap_pos hc
    gap_bound := by
      intro w hw
      apply hAcore.complement_lower (CuspParameters.core_contDiff hr).continuous
        hφ.1.2.1 hbound w
      simpa only [hv] using hw }
  exact hAcore.atomicGroundSimple_of_finrank_one cert.eigenspace_finrank

/-- The energy estimate and full original test gap hold for every normalized
core ground state, without selecting a phase or altering the gap constant. -/
theorem ground_with_gap {b : ℝ} {p : CuspParameters}
    (hRad : RadialCoreSpectralData b p) (hr : 0 < p.r₀) {coupling : ℝ}
    (hAcore : IsMagneticRealization b coupling p.core)
    (hT : hRad.threshold ≤ coupling) {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) :
    let e := (coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling
    e ≤ -1 + hRad.energyBound / coupling ∧
    ∀ u : Wavefunction, IsTestFunction u →
      (hRad.gap * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
        magneticForm b coupling p.core u - coupling ^ 2 * e * mass u := by
  obtain ⟨ψ, hψ, he, hgap⟩ := hRad.ground coupling hT
  obtain ⟨c, hc, hphase⟩ := hRad.core_groundSimple hr hAcore hT ψ φ hψ hφ
  refine ⟨he, ?_⟩
  intro u hu
  rw [hphase, norm_waveInner_smul_unit ψ u hc]
  exact hgap u hu

/-- A single positive radial normalized state has the energy estimate and
rank-one gap recorded by the radial spectral contract. -/
theorem positive_ground_with_gap {b : ℝ} {p : CuspParameters}
    (hRad : RadialCoreSpectralData b p) (hr : 0 < p.r₀) {coupling : ℝ}
    (hAcore : IsMagneticRealization b coupling p.core)
    (hT : hRad.threshold ≤ coupling) :
    ∃ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ ∧
    let e := (coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling
    e ≤ -1 + hRad.energyBound / coupling ∧
    ∀ u : Wavefunction, IsTestFunction u →
      (hRad.gap * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
        magneticForm b coupling p.core u - coupling ^ 2 * e * mass u := by
  obtain ⟨φ, hφ, hpos⟩ := hRad.positive_radial_ground coupling hT
  exact ⟨φ, hφ, hpos, hRad.ground_with_gap hr hAcore hT hφ⟩

end RadialCoreSpectralData
end InfiniteZero
