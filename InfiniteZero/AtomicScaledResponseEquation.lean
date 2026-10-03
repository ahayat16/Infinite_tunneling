import InfiniteZero.AtomicResponseDataJets

/-!
# The exact semiclassical equation for the atomic Schur response

Multiplication of the genuine response equation by the squared inverse
coupling gives exactly `atomicScaledResponseSource`. The normalized state,
Schur correction and phase are retained from the existing representative.
No estimate or additional spectral hypothesis is used in this rescaling.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

private theorem scaled_response_equation_of_response_equation
    {p : CuspParameters} {coupling c : ℝ} {φ η : Wavefunction}
    (hcoupling : 0 < coupling) {x : Plane}
    (heq : magneticHamiltonian p.b coupling p.potential η x -
      (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x =
      -((c * coupling ^ 2 : ℝ) : ℂ) * (p.atomicPerturbation x : ℂ) * φ x +
        ((c * (atomicGroundEnergy p.b p.potential coupling -
          atomicGroundEnergy p.b p.core coupling) : ℝ) : ℂ) * φ x) :
    (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
      (magneticHamiltonian p.b coupling p.potential η x -
        (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) =
      p.atomicScaledResponseSource coupling c φ x := by
  have hc : (coupling : ℂ) ≠ 0 := by exact_mod_cast hcoupling.ne'
  rw [heq]
  simp only [CuspParameters.atomicScaledResponseSource,
    CuspParameters.atomicScaledEnergyShift]
  push_cast
  field_simp

/-- The true full and core eigen-equations imply the exact response source,
with semiclassical energy shift `h² * (Efull - Ecore)` and `h = coupling⁻¹`.
The coefficient can be any real number. -/
theorem IsAtomicGroundState.scaled_response_equation
    {p : CuspParameters} {coupling : ℝ} {ψ φ : Wavefunction}
    (hψ : IsAtomicGroundState p.b p.potential coupling ψ)
    (hφ : IsAtomicGroundState p.b p.core coupling φ)
    (hcoupling : 0 < coupling) (c : ℝ) (x : Plane) :
    (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
      (magneticHamiltonian p.b coupling p.potential
          (fun y => ψ y - (c : ℂ) * φ y) x -
        (atomicGroundEnergy p.b p.potential coupling : ℂ) *
          (ψ x - (c : ℂ) * φ x)) =
      p.atomicScaledResponseSource coupling c φ x := by
  have hψ' : IsEigenfunction p.b coupling (p.core + p.atomicPerturbation)
      (atomicGroundEnergy p.b p.potential coupling) ψ := by
    simpa only [p.core_add_atomicPerturbation] using hψ.1
  apply scaled_response_equation_of_response_equation hcoupling
  simpa only [p.core_add_atomicPerturbation, Complex.ofReal_mul, Complex.ofReal_pow]
    using hψ'.response_equation hφ.1 (c : ℂ) x

/-- The already constructed smooth state and its normalized Schur correction
satisfy the scaled equation, with exactly the same normalization and phase. -/
theorem AtomicSchurReference.exists_scaled_responseWavefunction
    {p : CuspParameters} {hp : p.BasicConditions} {coupling gap : ℝ}
    (s : AtomicSchurReference p hp coupling gap)
    (q : QuantitativeSchurGroundCertificate
      (magneticOperator p.b coupling p.potential) s.vector
      (atomicGroundEnergy p.b p.potential coupling) gap)
    (hApot : IsMagneticRealization p.b coupling p.potential)
    (hcoupling : 0 < coupling) :
    ∃ ψ : Wavefunction, IsAtomicGroundState p.b p.potential coupling ψ ∧
      Represents (q.certificate.normalizedVector : L2Space) ψ ∧
      let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
      let η : Wavefunction := fun x => ψ x - (c : ℂ) * s.coreState x
      ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧
        Represents (q.normalizedCorrection : L2Space) η ∧
        ∀ x : Plane,
          (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
            (magneticHamiltonian p.b coupling p.potential η x -
              (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) =
            p.atomicScaledResponseSource coupling c s.coreState x := by
  obtain ⟨ψ, hψ, hrep, hηsmooth, hηLp, hηrep, hηeq⟩ :=
    s.exists_responseWavefunction q hApot
  refine ⟨ψ, hψ, hrep, hηsmooth, hηLp, hηrep, ?_⟩
  intro x
  exact scaled_response_equation_of_response_equation hcoupling (hηeq x)

end InfiniteZero
