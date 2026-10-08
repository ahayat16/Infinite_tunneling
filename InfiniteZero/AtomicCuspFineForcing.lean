import InfiniteZero.GenericCompactL2Bound
import InfiniteZero.WeightedWavefunctionL2
import InfiniteZero.CuspWeightedActionGain
import InfiniteZero.AtomicCuspWeightedGraph
import InfiniteZero.CuspFineForcingPointwise

/-!
# Fine forcing bounds for the actual weighted L² multiplier

The compact support and almost-everywhere representative of the actual
atomic perturbation are kept explicit. The proved pointwise exterior-kernel
bound is integrated over one fixed planar ball, with constants independent
of the energy, coupling, weight strength and represented state. The exact
action and any strictly smaller log-flat exponent are retained, with a
polynomial prefactor of order two. No spectral or resolvent result is assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace InfiniteZero

/-- The actual bounded atomic perturbation acts on the chosen representative. -/
theorem Represents.atomicPerturbationMul {p : CuspParameters}
    {u : L2Space} {φ : Wavefunction} (hu : Represents u φ) (hp : p.BasicConditions) :
    Represents (CuspParameters.atomicPerturbationMul hp u)
      (fun x => (p.atomicPerturbation x : ℂ) * φ x) := by
  filter_upwards [CuspParameters.coe_atomicPerturbationMul hp u, hu] with x hw hx
  simp only [hw, hx, CuspParameters.atomicPerturbation, Pi.sub_apply]

namespace CuspParameters

theorem cuspSupportRadius_pos {p : CuspParameters} (hp : p.BasicConditions) :
    0 < p.cuspSupportRadius := by
  unfold cuspSupportRadius
  have ht := hp.t₀_pos
  have hs := hp.s₀_pos
  positivity

/-- Multiplication by an arbitrary weight and state cannot enlarge the fixed
support of the two cusps. No smoothness or integrability is assumed here. -/
theorem weightedAtomicPerturbation_support_subset_closedBall
    {p : CuspParameters} (hp : p.BasicConditions) (weight φ : Wavefunction) :
    Function.support (fun x => weight x * (p.atomicPerturbation x : ℂ) * φ x) ⊆
      Metric.closedBall (0 : Plane) p.cuspSupportRadius := by
  intro x hx
  have hW : p.atomicPerturbation x ≠ 0 := by
    intro hzero
    exact hx (by simp [hzero])
  have hnorm := (atomicPerturbation_tsupport_norm_bounds hp (subset_tsupport _ hW)).2
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm

/-- Pointwise bounds on the physical weighted source transfer to the actual
weighted perturbation operator, using the exact area of the fixed support ball. -/
theorem norm_atomicExponentialWeightMul_atomicPerturbationMul_le
    {p : CuspParameters} (hp : p.BasicConditions) (T : Plane → ℝ) (hTc : Continuous T)
    {M : ℝ} (hT : ∀ x, T x ∈ Icc 0 M) (coupling κ : ℝ)
    {u : L2Space} {φ : Wavefunction} (hu : Represents u φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x,
      ‖(Real.exp (κ * coupling * T x) : ℂ) * (p.atomicPerturbation x : ℂ) * φ x‖ ≤ B) :
    ‖atomicExponentialWeightMul T hTc hT coupling κ (atomicPerturbationMul hp u)‖ ≤
      Real.sqrt Real.pi * p.cuspSupportRadius * B := by
  have hrep := (hu.atomicPerturbationMul hp).atomicExponentialWeightMul
    T hTc hT coupling κ
  have hrep' : Represents
      (atomicExponentialWeightMul T hTc hT coupling κ (atomicPerturbationMul hp u))
      (fun x => (Real.exp (κ * coupling * T x) : ℂ) *
        (p.atomicPerturbation x : ℂ) * φ x) := by
    simpa only [mul_assoc] using hrep
  exact hrep'.norm_le_sqrt_pi_mul_radius_mul_bound (cuspSupportRadius_pos hp).le
    (weightedAtomicPerturbation_support_subset_closedBall hp _ φ) hB hbound

/-- Fine forcing at semiclassical scale, for any actual L² vector whose same
representative has the prescribed exact exterior kernel tail. -/
theorem exists_atomic_cusp_fine_forcing_norm {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) {M : ℝ}
    (hT : ∀ x, χ.weight x ∈ Icc 0 M) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
        ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction,
          (∀ x, p.r₀ < ‖x‖ → φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ)) →
          ∀ u : L2Space, Represents u φ →
            ‖atomicExponentialWeightMul χ.weight χ.weight_continuous hT h⁻¹ κ
              (atomicPerturbationMul hp u)‖ ≤
              C * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
                Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) := by
  obtain ⟨C, hC, hpoint⟩ := exists_cusp_fine_forcing_pointwise hp χ hβ₁ hβ₁β
  have hr := cuspSupportRadius_pos hp
  refine ⟨Real.sqrt Real.pi * p.cuspSupportRadius * C, by positivity, ?_⟩
  filter_upwards [hpoint] with h hh
  intro E hE κ hκ Γ hΓ φ hφ u hu
  calc
    _ ≤ Real.sqrt Real.pi * p.cuspSupportRadius *
        (C * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
          Real.exp (-β₁ * (Real.log (1 / h)) ^ 2)) := by
      apply norm_atomicExponentialWeightMul_atomicPerturbationMul_le hp χ.weight
        χ.weight_continuous hT h⁻¹ κ hu (by positivity)
      simpa only [div_eq_mul_inv] using hh E hE κ hκ Γ hΓ φ hφ
    _ = _ := by ring

/-- Coupling-scale version: the constant and threshold precede the energy,
weight, exterior coefficient and represented state. This bounds `W φ`;
the unscaled Hamiltonian residual `coupling² W φ` has two additional powers
of the coupling. -/
theorem exists_atomic_cusp_fine_forcing_norm_coupling {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) {M : ℝ}
    (hT : ∀ x, χ.weight x ∈ Icc 0 M) :
    ∃ C > 0, ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
        ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction,
          (∀ x, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹ E ‖x‖ : ℂ)) →
          ∀ u : L2Space, Represents u φ →
            ‖atomicExponentialWeightMul χ.weight χ.weight_continuous hT coupling κ
              (atomicPerturbationMul hp u)‖ ≤
              C * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b E p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
  obtain ⟨C, hC, hh⟩ := exists_atomic_cusp_fine_forcing_norm hp χ hβ₁ hβ₁β hT
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (tendsto_inv_atTop_nhdsGT_zero.eventually hh)
  refine ⟨C, hC, max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro coupling hcoupling E hE κ hκ Γ hΓ φ hφ u hu
  have hbound := hN coupling ((le_max_left _ _).trans hcoupling)
    E hE κ hκ Γ hΓ φ hφ u hu
  simpa only [inv_inv, inv_pow, one_div, div_eq_mul_inv, mul_one, one_mul,
    mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hbound

end CuspParameters
end InfiniteZero
