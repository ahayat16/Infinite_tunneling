import InfiniteZero.AtomicGroundComparison
import InfiniteZero.SchurResponseEquation

/-!
# The physical wavefunction of the normalized atomic Schur response

The smooth full ground state represents exactly the normalized vector of the
given Schur certificate. Subtracting its reference component gives a smooth
L² representative of that certificate's domain correction. The uncompressed
differential equation is proved pointwise from the two true eigen-equations;
no elliptic estimate or pointwise decay is an additional input.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem Represents.sub {u v : L2Space} {ψ φ : Wavefunction}
    (hψ : Represents u ψ) (hφ : Represents v φ) : Represents (u - v) (ψ - φ) := by
  filter_upwards [Lp.coeFn_sub u v, hψ, hφ] with x hs hx hy
  simpa only [Pi.sub_apply, hx, hy] using hs

/-- Linear superposition with different potentials gives the exact response
equation, including the energy-shift term and its sign. -/
theorem IsEigenfunction.response_equation
    {b coupling E E₀ : ℝ} {V W : Potential} {ψ φ : Wavefunction}
    (hψ : IsEigenfunction b coupling (V + W) E ψ)
    (hφ : IsEigenfunction b coupling V E₀ φ) (c : ℂ) (x : Plane) :
    magneticHamiltonian b coupling (V + W) (fun y => ψ y - c * φ y) x -
      (E : ℂ) * (ψ x - c * φ x) =
      -(c * (coupling ^ 2 : ℂ)) * (W x : ℂ) * φ x +
        c * ((E - E₀ : ℝ) : ℂ) * φ x := by
  have hfun : (fun y => ψ y - c * φ y) = ψ + (-c) • φ := by
    ext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, sub_eq_add_neg]
  have hlinfun := magneticHamiltonian_add b coupling (V + W)
    (ψ := ψ) (χ := (-c) • φ) hψ.1 (hφ.1.const_smul (-c))
  rw [magneticHamiltonian_smul b coupling (V + W) hφ.1 (-c)] at hlinfun
  have hlin := congrFun hlinfun x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hlin
  have hpotential := congrFun (magneticHamiltonian_add_potential b coupling V W φ) x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpotential
  rw [hφ.2.2 x] at hpotential
  rw [hfun, hlin, hψ.2.2 x, hpotential]
  push_cast
  ring

/-- The prescribed normalized certificate vector, rather than a separately
chosen phase, has a genuine normalized smooth ground-state representative. -/
theorem GroundStateCertificate.exists_atomicGroundState_representative
    {b coupling : ℝ} {V : Potential}
    (q : GroundStateCertificate (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling))
    (hA : IsMagneticRealization b coupling V) :
    ∃ ψ : Wavefunction, IsAtomicGroundState b V coupling ψ ∧
      Represents (q.normalizedVector : L2Space) ψ := by
  have hv : (q.normalizedVector : L2Space) ∈ operatorEigenspace
      (magneticOperator b coupling V) (atomicGroundEnergy b V coupling) := by
    rw [mem_operatorEigenspace]
    exact q.normalizedVector_eigenvector ▸
      (magneticOperator b coupling V).mem_graph q.normalizedVector
  obtain ⟨ψ, hψ, hrep⟩ := (hA.eigenfunction_iff _ _).mp hv
  refine ⟨ψ, ⟨hψ, ?_⟩, hrep⟩
  rw [← hrep.norm_sq_eq_mass, q.normalizedVector_norm, one_pow]

/-- All conclusions refer to the same `q`, the same normalized smooth `ψ`
and the same core reference retained by `s`. In particular the correction
represents `q.normalizedCorrection` exactly, not just up to phase. -/
theorem AtomicSchurReference.exists_responseWavefunction
    {p : CuspParameters} {hp : p.BasicConditions} {coupling gap : ℝ}
    (s : AtomicSchurReference p hp coupling gap)
    (q : QuantitativeSchurGroundCertificate
      (magneticOperator p.b coupling p.potential) s.vector
      (atomicGroundEnergy p.b p.potential coupling) gap)
    (hApot : IsMagneticRealization p.b coupling p.potential) :
    ∃ ψ : Wavefunction, IsAtomicGroundState p.b p.potential coupling ψ ∧
      Represents (q.certificate.normalizedVector : L2Space) ψ ∧
      let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
      let η : Wavefunction := fun x => ψ x - (c : ℂ) * s.coreState x
      ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧
        Represents (q.normalizedCorrection : L2Space) η ∧
        ∀ x : Plane,
          magneticHamiltonian p.b coupling p.potential η x -
            (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x =
          -((c * coupling ^ 2 : ℝ) : ℂ) * (p.atomicPerturbation x : ℂ) * s.coreState x +
            ((c * (atomicGroundEnergy p.b p.potential coupling -
              atomicGroundEnergy p.b p.core coupling) : ℝ) : ℂ) * s.coreState x := by
  obtain ⟨ψ, hψ, hrep⟩ := q.certificate.exists_atomicGroundState_representative hApot
  refine ⟨ψ, hψ, hrep, ?_⟩
  let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
  let η : Wavefunction := fun x => ψ x - (c : ℂ) * s.coreState x
  change ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧
    Represents (q.normalizedCorrection : L2Space) η ∧ _
  have hη : Represents (q.normalizedCorrection : L2Space) η := by
    rw [q.normalizedCorrection_coe]
    exact hrep.sub (s.represents.smul (c : ℂ))
  refine ⟨hψ.1.1.sub (contDiff_const.mul s.coreGround.1.1), hη.memLp, hη, ?_⟩
  intro x
  have hψ' : IsEigenfunction p.b coupling (p.core + p.atomicPerturbation)
      (atomicGroundEnergy p.b p.potential coupling) ψ := by
    simpa only [p.core_add_atomicPerturbation] using hψ.1
  have heq := hψ'.response_equation s.coreGround.1 (c : ℂ) x
  simpa only [p.core_add_atomicPerturbation, Complex.ofReal_mul, Complex.ofReal_pow,
    η] using heq

end InfiniteZero
