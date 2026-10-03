import InfiniteZero.AtomicWeightedTail
import InfiniteZero.AtomicResidualDecay

/-!
# Exponential decay of the true weighted atomic residual

Multiplication by the actual bounded weight costs at most `exp (κ λ M)`.
The unweighted residual already decays as `C λ exp (-d λ)`. Choosing
`κ` in a fixed sufficiently small interval preserves half of this
exponential rate, uniformly in the coupling, state and L² representative.
Only continuity and `0 ≤ T ≤ M` are needed; no operator-domain preservation
or vanishing of the weight near the core is assumed.
-/

noncomputable section
open Set

namespace InfiniteZero

/-- Norm bound for the genuine exponential multiplier, allowing either sign
of the coupling and weight strength. -/
theorem norm_atomicExponentialWeightMul_apply_le
    (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ) (u : L2Space) :
    ‖atomicExponentialWeightMul T hTc hT coupling κ u‖ ≤
      Real.exp (|κ * coupling| * M) * ‖u‖ :=
  norm_boundedPotentialMul_apply_le _ _
    (abs_atomicExponentialWeight_le hT coupling κ) u

theorem norm_atomicExponentialWeightMul_apply_le_of_nonneg
    (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) {coupling κ : ℝ}
    (hc : 0 ≤ coupling) (hκ : 0 ≤ κ) (u : L2Space) :
    ‖atomicExponentialWeightMul T hTc hT coupling κ u‖ ≤
      Real.exp (κ * coupling * M) * ‖u‖ := by
  simpa only [abs_of_nonneg (mul_nonneg hκ hc)] using
    norm_atomicExponentialWeightMul_apply_le T hTc hT coupling κ u

namespace CuspParameters

/-- The weighted residual is the actual cusp perturbation of the same L²
vector. This estimate requires no eigenfunction hypothesis. -/
theorem norm_atomicWeightedResidual_le {p : CuspParameters}
    (hp : p.BasicConditions) (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) {coupling κ : ℝ}
    (hc : 0 ≤ coupling) (hκ : 0 ≤ κ) (u : L2Space) :
    ‖atomicExponentialWeightMul T hTc hT coupling κ
      ((coupling ^ 2 : ℂ) • atomicPerturbationMul hp u)‖ ≤
      Real.exp (κ * coupling * M) *
        ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ :=
  norm_atomicExponentialWeightMul_apply_le_of_nonneg T hTc hT hc hκ _

/-- Uniform exponential decay for the actual weighted residual of every
normalized core ground state, with all constants chosen before the coupling,
the weight strength, the state and its L² representative. -/
theorem exists_atomicWeightedResidual_decay_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (T : Plane → ℝ) (hTc : Continuous T) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ x, T x ∈ Icc 0 M) :
    ∃ κ₀ > 0, ∃ c > 0, ∃ C > 0, ∃ N > 0,
      ∀ coupling : ℝ, N ≤ coupling → ∀ κ ∈ Icc 0 κ₀,
        ∀ φ, IsAtomicGroundState p.b p.core coupling φ →
          ∀ u : L2Space, Represents u φ →
            ‖atomicExponentialWeightMul T hTc hT coupling κ
              ((coupling ^ 2 : ℂ) • atomicPerturbationMul hp u)‖ ≤
              C * coupling * Real.exp (-c * coupling) := by
  obtain ⟨K, hK, d, hd, N, hN, hres⟩ :=
    exists_atomicResidual_decay_of_radialData hp hRad hAcore hApot
  let κ₀ := d / (2 * (M + 1))
  have hden : 0 < 2 * (M + 1) := by positivity
  have hκ₀ : 0 < κ₀ := div_pos hd hden
  refine ⟨κ₀, hκ₀, d / 2, half_pos hd, K, hK, N, hN, ?_⟩
  intro coupling hc κ hκ φ hφ u hu
  have hcpos : 0 < coupling := hN.trans_le hc
  have hκM : κ * M ≤ d / 2 := by
    have hratio : κ₀ * (M + 1) = d / 2 := by
      dsimp only [κ₀]
      field_simp
    have hm := mul_le_mul_of_nonneg_right hκ.2 hM
    nlinarith only [hm, hratio, hκ₀.le]
  calc
    ‖atomicExponentialWeightMul T hTc hT coupling κ
        ((coupling ^ 2 : ℂ) • atomicPerturbationMul hp u)‖ ≤
        Real.exp (κ * coupling * M) *
          ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ :=
      norm_atomicWeightedResidual_le hp T hTc hT hcpos.le hκ.1 u
    _ ≤ Real.exp (κ * coupling * M) *
        (K * coupling * Real.exp (-d * coupling)) :=
      mul_le_mul_of_nonneg_left (hres coupling hc φ hφ u hu) (Real.exp_pos _).le
    _ = K * coupling * Real.exp ((κ * M - d) * coupling) := by
      rw [show Real.exp (κ * coupling * M) *
          (K * coupling * Real.exp (-d * coupling)) =
          K * coupling * (Real.exp (κ * coupling * M) * Real.exp (-d * coupling)) by ring,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ K * coupling * Real.exp (-(d / 2) * coupling) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK.le hcpos.le)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by linarith only [hκM]) hcpos.le

end CuspParameters
end InfiniteZero
