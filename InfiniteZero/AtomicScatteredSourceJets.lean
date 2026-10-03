import InfiniteZero.AtomicFineResponseJets
import InfiniteZero.CuspScatteredSourceJets

/-!
# The two log-flat factors of the actual scattered atomic source

The source is the existing `atomicSource` applied to the true correction,
not an independent function satisfying an assumed bound. The global and
local logarithmic margins are chosen independently. The same radial state,
full ground state, coefficient c and exterior coefficient Γ work on both
closed cusp supports, for every jet up to the fixed maximal order.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1200000

theorem exists_atomicGround_scattered_source_jets_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {βglobal βlocal : ℝ}
    (hg : 0 < βglobal) (hgβ : βglobal < p.β)
    (hl : 0 < βlocal) (hlβ : βlocal < p.β) (n : ℕ) :
    ∃ κ₀ > 0, ∃ Cη > 0, ∃ Csc > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let f : Wavefunction := p.atomicScaledResponseSource coupling c φ
          let A : ℝ := c * Γ *
            Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
            Real.exp (-βglobal * (Real.log coupling) ^ 2)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ ContDiff ℝ ∞ f ∧
          waveInner φ η = 0 ∧
          (∀ x : Plane,
            (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
              (magneticHamiltonian p.b coupling p.potential η x -
                (atomicGroundEnergy p.b p.potential coupling : ℂ) * η x) = f x) ∧
          ∀ κ ∈ Icc 0 κ₀, ∀ j : ℕ, j ≤ n →
            (∀ x ∈ closure p.cuspPacketInnerNeighborhood,
              Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j η x‖ ≤ Cη * coupling ^ 4 * A) ∧
            (∀ x ∈ tsupport p.cuspPlus,
              (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
                Csc * coupling ^ 6 * A * logFlat βlocal p.tStar (p.normalCoordinate x) *
                  Real.exp (-κ * coupling * p.normalCoordinate x)) ∧
            (∀ x ∈ tsupport p.cuspMinus,
              (coupling⁻¹) ^ j *
                ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
                Csc * coupling ^ 6 * A *
                  logFlat βlocal p.tStar (p.normalCoordinate (reflection x)) *
                  Real.exp (-κ * coupling * p.normalCoordinate (reflection x))) := by
  obtain ⟨κ₀, hκ₀, Cη, hCη, T, hT, hstates⟩ :=
    exists_atomicGround_fine_response_jets_of_radialData
      hInterior hp hRad hAcore hApot χ hg hgβ n
  obtain ⟨Cq, hCq, hsource⟩ :=
    exists_cusp_scattered_source_jet_bound hp χ hl hlβ n
  refine ⟨κ₀, hκ₀, Cη, hCη, Cq * Cη, mul_pos hCq hCη,
    max T 1, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcT : T ≤ coupling := (le_max_left _ _).trans hc
  have hc1 : 1 ≤ coupling := (le_max_right _ _).trans hc
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, hfsmooth, horth, heq, hjets⟩ := hstates coupling hcT
  let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
  let A : ℝ := c * Γ *
    Real.exp (-coupling * bridgeAction p.b
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
    Real.exp (-βglobal * (Real.log coupling) ^ 2)
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hcRange.1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, hfsmooth, horth, heq, ?_⟩
  intro κ hκ j hj
  have hresponse : ∀ k : ℕ, k ≤ n → ∀ x ∈ closure p.cuspPacketInnerNeighborhood,
      Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ k *
        ‖iteratedFDeriv ℝ k η x‖ ≤ Cη * coupling ^ 4 * A := by
    intro k hk x hx
    convert hjets κ hκ k hk x hx using 1
    dsimp [A, η]
    ring
  have hsc := hsource coupling hc1 κ η hηsmooth
    (Cη * coupling ^ 4 * A) (by positivity) hresponse j hj
  refine ⟨hresponse j hj, ?_, ?_⟩
  · intro x hx
    convert hsc.1 x hx using 1
    dsimp [A, η]
    ring
  · intro x hx
    convert hsc.2 x hx using 1
    dsimp [A, η]
    ring

end InfiniteZero.CuspParameters
