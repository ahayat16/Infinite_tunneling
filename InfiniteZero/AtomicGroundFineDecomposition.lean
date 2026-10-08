import InfiniteZero.AtomicGroundFineResponse
import InfiniteZero.AtomicResponseWavefunction
import InfiniteZero.WeightedWavefunctionL2

/-!
# The fine weighted response as a decomposition of genuine wavefunctions

The positive radial reference and its exact exterior coefficient are the
same ones used to construct the full ground state. The physical correction
is orthogonal to that reference, satisfies the uncompressed PDE pointwise,
and has the squared fine weighted response bound as its actual mass bound.
All constants precede the coupling; both states, their normalization and
their exterior coefficient precede the weight strength.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1600000

theorem exists_atomicGround_fine_weighted_decomposition_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) :
    ∃ M > 0, ∃ _hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          waveInner φ η = 0 ∧
          (∀ κ ∈ Icc 0 κ₀,
            mass (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * η x) ≤
              (C * c * Γ * coupling ^ 3 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2) ∧
          ∀ x : Plane,
            magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x =
              -((c * coupling ^ 2 : ℝ) : ℂ) * (p.atomicPerturbation x : ℂ) * φ x +
                ((c * (atomicGroundEnergy p.b p.potential coupling -
                  atomicGroundEnergy p.b p.core coupling) : ℝ) : ℂ) * φ x := by
  obtain ⟨M, hM, hT, κ₀, hκ₀, C, hC, threshold, hthreshold, hstates⟩ :=
    exists_atomicGround_fine_weighted_response_of_radialData hp hRad hAcore hApot χ hβ₁ hβ₁β
  refine ⟨M, hM, hT, κ₀, hκ₀, C, hC, threshold, hthreshold, ?_⟩
  intro coupling hc
  obtain ⟨s, hpos, q, hnormal, Γ, hΓ, htail, hresponse⟩ := hstates coupling hc
  obtain ⟨ψ, hψ, _, _, _, hηrep, hηeq⟩ := s.exists_responseWavefunction q (hApot coupling)
  let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
  refine ⟨s.coreState, ψ, s.coreGround, hpos, hψ, c, hnormal, Γ, hΓ, htail,
    ?_, ?_, hηeq⟩
  · have horth := q.normalizedCorrection_orthogonal s.vector_norm
    rwa [s.represents.inner_eq_waveInner hηrep] at horth
  · intro κ hκ
    rw [hηrep.mass_atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ]
    exact pow_le_pow_left₀ (norm_nonneg _) (hresponse κ hκ) 2

end InfiniteZero.CuspParameters
