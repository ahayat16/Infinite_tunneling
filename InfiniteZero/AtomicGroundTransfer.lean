import InfiniteZero.WavefunctionL2Bridge
import InfiniteZero.HoppingPhase
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Transfer of actual operator ground states to smooth wavefunctions

The hypotheses concern the concrete operator eigenspace at the previously
defined variational bottom. These lemmas do not assert that a ground
eigenvector exists or that its eigenspace has dimension one.
-/

noncomputable section

open MeasureTheory

namespace InfiniteZero

theorem Represents.smul {u : L2Space} {ψ : Wavefunction} (hu : Represents u ψ)
    (c : ℂ) : Represents (c • u) (c • ψ) := by
  filter_upwards [Lp.coeFn_smul c u, hu] with x hc hx
  exact hc.trans (congrArg (fun z : ℂ => c • z) hx)

/-- Operator multiplicity one implies uniqueness of normalized smooth ground
states up to a scalar of norm one, with equality at every point. -/
theorem IsMagneticRealization.atomicGroundSimple_of_finrank_one
    {b coupling : ℝ} {V : Potential} (hA : IsMagneticRealization b coupling V)
    (hdim : Module.finrank ℂ (operatorEigenspace (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling)) = 1) :
    AtomicGroundSimple b V coupling := by
  intro φ ψ hφ hψ
  let G := operatorEigenspace (magneticOperator b coupling V)
    (atomicGroundEnergy b V coupling)
  let u : L2Space := hφ.1.2.1.toLp φ
  let v : L2Space := hψ.1.2.1.toLp ψ
  have hu : Represents u φ := represents_toLp hφ.1.2.1
  have hv : Represents v ψ := represents_toLp hψ.1.2.1
  have huG : u ∈ G :=
    (hA.eigenfunction_iff _ u).mpr ⟨φ, hφ.1, hu⟩
  have hvG : v ∈ G :=
    (hA.eigenfunction_iff _ v).mpr ⟨ψ, hψ.1, hv⟩
  have huNe : u ≠ 0 := hu.ne_zero_of_mass_one hφ.2
  have huGNe : (⟨u, huG⟩ : G) ≠ 0 := by
    intro hzero
    exact huNe (congrArg Subtype.val hzero)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim huGNe (⟨v, hvG⟩ : G)
  have hcu : c • u = v := congrArg Subtype.val hc
  have huNorm : ‖u‖ = 1 := by
    have hs : ‖u‖ ^ 2 = 1 := hu.norm_sq_eq_mass.trans hφ.2
    nlinarith [norm_nonneg u]
  have hvNorm : ‖v‖ = 1 := by
    have hs : ‖v‖ ^ 2 = 1 := hv.norm_sq_eq_mass.trans hψ.2
    nlinarith [norm_nonneg v]
  have hcNorm : ‖c‖ = 1 := by
    have hnorm := congrArg norm hcu
    simpa only [norm_smul, huNorm, hvNorm, mul_one] using hnorm
  have hcv : Represents v (c • φ) := hcu ▸ hu.smul c
  have hEq : ψ = c • φ := Measure.eq_of_ae_eq (hv.symm.trans hcv)
    hψ.1.1.continuous (hφ.1.1.continuous.const_smul c)
  exact ⟨c, hcNorm, hEq⟩

/-- A nonzero actual ground eigenvector can be normalized in L² before choosing
its smooth representative. No compact support is required of this eigenvector. -/
theorem IsMagneticRealization.exists_atomicGroundState_of_eigenvector
    {b coupling : ℝ} {V : Potential} (hA : IsMagneticRealization b coupling V)
    {u : L2Space}
    (hu : u ∈ operatorEigenspace (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling)) (huNe : u ≠ 0) :
    ∃ φ, IsAtomicGroundState b V coupling φ := by
  let c : ℂ := (‖u‖⁻¹ : ℝ)
  let w : L2Space := c • u
  have hw : w ∈ operatorEigenspace (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling) :=
    (operatorEigenspace (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling)).smul_mem c hu
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr huNe
  have hwNorm : ‖w‖ = 1 := by
    simp only [w, c, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn
  obtain ⟨φ, hφ, hwφ⟩ := (hA.eigenfunction_iff _ w).mp hw
  refine ⟨φ, hφ, ?_⟩
  rw [← hwφ.norm_sq_eq_mass, hwNorm]
  norm_num

end InfiniteZero
