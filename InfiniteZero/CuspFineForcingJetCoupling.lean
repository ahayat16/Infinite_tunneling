import InfiniteZero.CuspFineForcingJets

/-! A common coupling threshold for the pointwise jets of the actual force. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

theorem exists_cusp_fine_forcing_jets_pointwise_coupling
    {p : CuspParameters} (hp : p.BasicConditions) (χ : CuspWeightCutoffs p)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) (n : ℕ) :
    ∃ C > 0, ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
      ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction, ContDiff ℝ ∞ φ →
      (∀ x, p.r₀ < ‖x‖ →
        φ x = (Γ * landauKernel p.b coupling⁻¹ E ‖x‖ : ℂ)) →
      ∀ j : ℕ, j ≤ n → ∀ x : Plane,
        Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
          ‖iteratedFDeriv ℝ j (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ ≤
          C * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b E p.R) *
            Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
  choose C hC hforce using fun j : ℕ =>
    exists_cusp_fine_forcing_jet_bound hp χ hβ₁ hβ₁β j
  have hall := (eventually_all_finset (Finset.range (n + 1))).mpr (fun j _ => hforce j)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (tendsto_inv_atTop_nhdsGT_zero.eventually hall)
  let Csum := 1 + ∑ j ∈ Finset.range (n + 1), C j
  have hCsum : 0 < Csum := by
    have hs : 0 ≤ ∑ j ∈ Finset.range (n + 1), C j :=
      Finset.sum_nonneg (fun j _ => (hC j).le)
    dsimp [Csum]
    linarith
  refine ⟨Csum, hCsum, max N 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hc E hE κ hκ Γ hΓ φ hφ htail j hj x
  have hjmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hCj : C j ≤ Csum := by
    have hs := Finset.single_le_sum (fun i _ => (hC i).le) hjmem
    dsimp [Csum]
    linarith
  have hjbound := hN coupling ((le_max_left _ _).trans hc) j hjmem
    E hE κ hκ Γ hΓ φ hφ htail x
  have hm : Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
      ‖iteratedFDeriv ℝ j (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ ≤
      C j * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b E p.R) *
        Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
    simpa only [inv_inv, inv_pow, one_div, div_eq_mul_inv, mul_one, one_mul,
      mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hjbound
  exact hm.trans (by gcongr)

end InfiniteZero.CuspParameters
