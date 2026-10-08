import InfiniteZero.AtomicGroundRankOne

/-!
# From operator spectral data to normalized atomic states

A smooth representative of the normalized vector in a ground-state
certificate is a pointwise normalized atomic eigenfunction. The operator
gap then gives the rank-one inequality on compactly supported test
functions, with the same gap constant.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- A prescribed smooth representative of the certificate's normalized
vector solves the atomic eigenvalue equation at the variational bottom. -/
theorem GroundStateCertificate.isAtomicGroundState_of_smooth_representative
    {b coupling E : ℝ} {V : Potential}
    (q : GroundStateCertificate (magneticOperator b coupling V) E)
    (hA : IsMagneticRealization b coupling V)
    {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ)
    (hrep : Represents (q.normalizedVector : L2Space) φ) :
    IsAtomicGroundState b V coupling φ := by
  have hE := hA.atomicGroundEnergy_eq_of_certificate q
  subst E
  obtain ⟨ψ, hψ, hψrep⟩ := q.exists_atomicGroundState_representative hA
  have heq : ψ = φ := Measure.eq_of_ae_eq (hψrep.symm.trans hrep)
    hψ.1.1.continuous hφ.continuous
  exact heq ▸ hψ

/-- The operator gap transfers to every test function using the prescribed
smooth representative; no energy estimate or test inequality is assumed. -/
theorem GroundStateCertificate.atomic_test_rankOne_lower_bound_of_smooth_representative
    {b coupling E : ℝ} {V : Potential}
    (q : GroundStateCertificate (magneticOperator b coupling V) E)
    (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ)
    (hrep : Represents (q.normalizedVector : L2Space) φ)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    q.gap * (mass ψ - ‖waveInner φ ψ‖ ^ 2) ≤
      magneticForm b coupling V ψ - atomicGroundEnergy b V coupling * mass ψ := by
  have hE := hA.atomicGroundEnergy_eq_of_certificate q
  subst E
  exact q.atomic_test_rankOne_lower_bound hA hV
    (q.isAtomicGroundState_of_smooth_representative hA hφ hrep) hψ

end InfiniteZero
