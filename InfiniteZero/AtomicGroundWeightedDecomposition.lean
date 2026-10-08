import InfiniteZero.AtomicGroundWeightedDecay
import InfiniteZero.AtomicResponseWavefunction
import InfiniteZero.WeightedWavefunctionL2

/-!
# Physical weighted decomposition of the actual atomic ground state

The positive radial core state and the full ground state are genuine smooth
normalized wavefunctions. Their same correction is orthogonal to the core,
has exponentially small weighted mass, and satisfies the exact uncompressed
differential equation. All constants precede the coupling and both states
precede the weight strength. No tunneling-scale estimate is claimed here.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1600000

theorem exists_atomicGround_weighted_decomposition_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) :
    ∃ M > 0, ∃ _hT : ∀ x, χ.weight x ∈ Icc 0 M,
      ∃ κ₀ > 0, ∃ C > 0, ∃ d > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1,
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          waveInner φ η = 0 ∧
          (∀ κ ∈ Icc 0 κ₀,
            mass (fun x => (Real.exp (κ * coupling * χ.weight x) : ℂ) * η x) ≤
              C ^ 2 * Real.exp (-2 * d * coupling)) ∧
          ∀ x : Plane,
            magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x =
              -((c * coupling ^ 2 : ℝ) : ℂ) * (p.atomicPerturbation x : ℂ) * φ x +
                ((c * (atomicGroundEnergy p.b p.potential coupling -
                  atomicGroundEnergy p.b p.core coupling) : ℝ) : ℂ) * φ x := by
  obtain ⟨M, hM, hT, κ₀, hκ₀, C, hC, d, hd, threshold, hthreshold, hstates⟩ :=
    exists_atomicGround_weighted_decay_of_radialData hp hRad hAcore hApot χ
  refine ⟨M, hM, hT, κ₀, hκ₀, C, hC, d, hd, threshold, hthreshold, ?_⟩
  intro coupling hc
  obtain ⟨s, hpos, q, hnormal, hdecay⟩ := hstates coupling hc
  obtain ⟨ψ, hψ, _, _, _, hηrep, hηeq⟩ := s.exists_responseWavefunction q (hApot coupling)
  let c := schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))
  refine ⟨s.coreState, ψ, s.coreGround, hpos, hψ, c, hnormal, ?_, ?_, hηeq⟩
  · have horth := q.normalizedCorrection_orthogonal s.vector_norm
    rwa [s.represents.inner_eq_waveInner hηrep] at horth
  · intro κ hκ
    rw [hηrep.mass_atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hdecay κ hκ) 2
    have hexp : Real.exp (-d * coupling) ^ 2 = Real.exp (-2 * d * coupling) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow, hexp] using h

end InfiniteZero.CuspParameters
