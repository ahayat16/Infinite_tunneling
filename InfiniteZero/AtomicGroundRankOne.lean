import InfiniteZero.GroundStateRankOne
import InfiniteZero.MagneticTestRankOne
import InfiniteZero.AtomicGroundConstruction
import InfiniteZero.AtomicResponseWavefunction
import InfiniteZero.RadialCoreGroundChoice

/-!
# The full atomic ground state carries the quantitative rank-one test gap

The Schur certificate already contains a gap of `hRad.gap / 2 * coupling`.
Projection onto its normalized eigenvector gives the full rank-one bound,
which applies to every test function through the actual operator graph.
Simplicity transfers the same bound to every normalized full ground state,
without any choice of phase and without loss in the gap constant.
-/

noncomputable section
namespace InfiniteZero

/-- Every normalized physical ground state carries the exact gap of a
certificate at the actual atomic energy. -/
theorem GroundStateCertificate.atomic_test_rankOne_lower_bound
    {b coupling : ℝ} {V : Potential}
    (q : GroundStateCertificate (magneticOperator b coupling V)
      (atomicGroundEnergy b V coupling))
    (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {φ : Wavefunction} (hφ : IsAtomicGroundState b V coupling φ)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    q.gap * (mass ψ - ‖waveInner φ ψ‖ ^ 2) ≤
      magneticForm b coupling V ψ - atomicGroundEnergy b V coupling * mass ψ := by
  obtain ⟨φ₀, hφ₀, hrep⟩ := q.exists_atomicGroundState_representative hA
  have hs := (hA.atomicGround_properties_of_certificate q).2.1
  obtain ⟨z, hz, hphase⟩ := hs φ₀ φ hφ₀ hφ
  rw [hphase, norm_waveInner_smul_unit φ₀ ψ hz]
  have h := hA.test_rankOne_lower_of_operator hV hrep
    (c := q.gap) (k := q.gap) (E := atomicGroundEnergy b V coupling)
    (fun u => by simpa only [mul_sub] using q.rankOne_lower_bound hA.selfAdjoint u) hψ
  simpa only [mul_sub] using h

namespace CuspParameters

/-- The same quantitative rank-one inequality holds for every true full
atomic ground state, at a threshold fixed before that state is chosen. -/
theorem exists_atomic_test_rankOne_gap_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ ψ : Wavefunction, IsTestFunction ψ →
        (hRad.gap / 2 * coupling) * (mass ψ - ‖waveInner φ ψ‖ ^ 2) ≤
          magneticForm p.b coupling p.potential ψ -
            atomicGroundEnergy p.b p.potential coupling * mass ψ := by
  obtain ⟨T, hT, hcert⟩ := exists_atomicGroundCertificate_of_radialData hp hRad hAcore hApot
  refine ⟨T, hT, ?_⟩
  intro coupling hc φ hφ ψ hψ
  obtain ⟨E, _, q, hgap⟩ := hcert coupling hc
  have hE := (hApot coupling).atomicGroundEnergy_eq_of_certificate q
  subst E
  rw [← hgap]
  exact q.atomic_test_rankOne_lower_bound (hApot coupling)
    (admissiblePotential hp).smooth.continuous hφ hψ

end CuspParameters
end InfiniteZero
