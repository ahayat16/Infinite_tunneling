import InfiniteZero.AtomicPerturbationTail
import InfiniteZero.AtomicGroundAgmon

/-!
# Exponential decay of the actual radial-core residual

The exterior Agmon estimate and the actual cusp multiplier bound combine
to give `K λ exp(-d λ)` for the residual of every normalized radial-core
ground state in the full atomic operator. The constants are chosen before
the coupling or the ground state. No new decay or spectral assumption enters.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero.CuspParameters

/-- Conversion of an exterior-mass estimate to the norm of the true residual. -/
theorem norm_scaled_atomicPerturbationMul_le_of_exterior_mass {p : CuspParameters}
    (hp : p.BasicConditions) {coupling C d : ℝ} (hc : 0 < coupling) (hC : 0 ≤ C)
    {u : L2Space} {φ : Wavefunction} (hu : Represents u φ)
    (htail : (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
      (C / coupling ^ 2) * Real.exp (-2 * d * coupling)) :
    ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ ≤
      (2 * p.ε * p.a * Real.sqrt C) * coupling * Real.exp (-d * coupling) := by
  have hexp : Real.exp (-2 * d * coupling) = Real.exp (-d * coupling) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquare := (norm_scaled_atomicPerturbationMul_sq_le_exterior hp coupling hu).trans
    (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
  have halgebra : (2 * coupling ^ 2 * p.ε * p.a) ^ 2 *
      ((C / coupling ^ 2) * Real.exp (-2 * d * coupling)) =
      ((2 * p.ε * p.a * Real.sqrt C) * coupling * Real.exp (-d * coupling)) ^ 2 := by
    rw [hexp]
    simp only [mul_pow, Real.sq_sqrt hC]
    field_simp
  rw [halgebra] at hsquare
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hp.ε_pos.le) hp.a_pos.le)
        (Real.sqrt_nonneg _)) hc.le) (Real.exp_pos _).le)).mp hsquare

/-- Uniform constants for every genuine radial-core ground state and every
L² representative of it. The realizations and radial spectral data are the
same explicit inputs used to construct the full ground state. -/
theorem exists_atomicResidual_decay_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ K > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ, IsAtomicGroundState p.b p.core coupling φ →
        ∀ u : L2Space, Represents u φ →
          ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ ≤
            K * coupling * Real.exp (-d * coupling) := by
  obtain ⟨C, hC, d, hd, T, hT, htail⟩ :=
    exists_atomicGround_agmon_tail_of_radialData hp hRad hAcore hApot
  refine ⟨2 * p.ε * p.a * Real.sqrt C,
    mul_pos (mul_pos (mul_pos (by norm_num) hp.ε_pos) hp.a_pos)
      (Real.sqrt_pos.mpr hC), d, hd, T, hT, ?_⟩
  intro coupling hc φ hφ u hu
  exact norm_scaled_atomicPerturbationMul_le_of_exterior_mass hp (hT.trans_le hc) hC.le hu
    ((htail coupling hc).2.2 φ hφ)

/-- The corresponding squared norm estimate, with the same polynomial order
and doubled exponential rate. -/
theorem exists_atomicResidual_sq_decay_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ K > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ, IsAtomicGroundState p.b p.core coupling φ →
        ∀ u : L2Space, Represents u φ →
          ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ ^ 2 ≤
            K ^ 2 * coupling ^ 2 * Real.exp (-2 * d * coupling) := by
  obtain ⟨K, hK, d, hd, T, hT, hbound⟩ :=
    exists_atomicResidual_decay_of_radialData hp hRad hAcore hApot
  refine ⟨K, hK, d, hd, T, hT, ?_⟩
  intro coupling hc φ hφ u hu
  have h := pow_le_pow_left₀ (norm_nonneg _) (hbound coupling hc φ hφ u hu) 2
  have hexp : Real.exp (-d * coupling) ^ 2 = Real.exp (-2 * d * coupling) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, hexp] using h

end InfiniteZero.CuspParameters
