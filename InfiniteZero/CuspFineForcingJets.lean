import InfiniteZero.ConstructionCuspJetBounds
import InfiniteZero.CuspWeightedActionGain
import InfiniteZero.ExteriorRadialJetBounds
import InfiniteZero.LogFlatWeightedAction

/-!
# Fine pointwise estimates for all jets of the genuine cusp forcing

The derivative estimate is for the actual product of the perturbation and
the exterior radial state. The exponential weight is applied after taking
the derivatives. Leibniz, the cusp jet margin and the radial kernel jets
retain the full action and every strict log-flat margin.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 800000

private theorem norm_jet_smul_le_of_bounds
    {q : Potential} {φ : Wavefunction} (hq : ContDiff ℝ ∞ q)
    (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (x : Plane)
    (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) {L M : ℝ} (hL : 0 ≤ L)
    (hqbound : ∀ i ≤ n, ‖iteratedFDeriv ℝ i q x‖ ≤ A i * L)
    (hφbound : ∀ j ≤ n, ‖iteratedFDeriv ℝ j φ x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => q y • φ y) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i) * L * M := by
  apply (norm_iteratedFDeriv_smul_le (contDiff_infty.mp hq n)
    (contDiff_infty.mp hφ n) x le_rfl).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (A i * L) * M := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hqbound i hin) (Nat.cast_nonneg _))
        (hφbound (n - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) hL))
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem cusp_product_jet_zero_off_tsupport
    {q : Potential} {φ : Wavefunction} {x : Plane}
    (hx : x ∉ tsupport q) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => q y • φ y) x = 0 := by
  by_contra hn
  exact hx (tsupport_smul_subset_left q φ (support_iteratedFDeriv_subset n hn))

private theorem norm_atomicPerturbation_product_jet_le
    {p : CuspParameters} (hp : p.BasicConditions) {φ : Wavefunction}
    (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (x : Plane) :
    ‖iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ ≤
      p.ε * (‖iteratedFDeriv ℝ n (fun y => p.cuspPlus y • φ y) x‖ +
        ‖iteratedFDeriv ℝ n (fun y => p.cuspMinus y • φ y) x‖) := by
  have hplus : ContDiff ℝ ∞ (fun y => p.cuspPlus y • φ y) :=
    (cuspPlus_contDiff hp).smul hφ
  have hminus : ContDiff ℝ ∞ (fun y => p.cuspMinus y • φ y) :=
    (cuspMinus_contDiff hp).smul hφ
  have heq : (fun y => (p.atomicPerturbation y : ℂ) * φ y) =
      fun y => p.ε • (p.cuspPlus y • φ y + p.cuspMinus y • φ y) := by
    funext y
    simp only [atomicPerturbation, Pi.sub_apply, potential, add_sub_cancel_left,
      Complex.ofReal_mul, Complex.ofReal_add, Complex.real_smul]
    ring
  rw [heq, iteratedFDeriv_const_smul_apply' (a := p.ε)
      (contDiff_infty.mp (hplus.add hminus) n).contDiffAt,
    fun_iteratedFDeriv_add_apply (contDiff_infty.mp hplus n).contDiffAt
      (contDiff_infty.mp hminus n).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_pos hp.ε_pos]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hp.ε_pos.le

private theorem weighted_jet_smul_le_of_bounds
    {q : Potential} {φ : Wavefunction} (hq : ContDiff ℝ ∞ q)
    (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (x : Plane) (A : ℕ → ℝ)
    (hA : ∀ i, 0 ≤ A i) {h C Γ L S w J J₀ G : ℝ}
    (hh : 0 < h) (hC : 0 ≤ C) (hΓ : 0 ≤ Γ) (hL : 0 ≤ L)
    (hS : 0 ≤ S)
    (hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i) ≤ S)
    (hqbound : ∀ i ≤ n, ‖iteratedFDeriv ℝ i q x‖ ≤ A i * L)
    (hφbound : ∀ j ≤ n, ‖iteratedFDeriv ℝ j φ x‖ ≤
      C * Γ * (h ^ (n + 2))⁻¹ * Real.exp (-J / h))
    (hgain : Real.exp (w / h) * L * Real.exp (-J / h) ≤ Real.exp (-J₀ / h) * G) :
    Real.exp (w / h) * h ^ n * ‖iteratedFDeriv ℝ n (fun y => q y • φ y) x‖ ≤
      S * C * Γ * (h ^ 2)⁻¹ * Real.exp (-J₀ / h) * G := by
  have hprod := norm_jet_smul_le_of_bounds hq hφ n x A hA hL hqbound hφbound
  have hM : 0 ≤ C * Γ * (h ^ (n + 2))⁻¹ * Real.exp (-J / h) := by positivity
  have hprod' : ‖iteratedFDeriv ℝ n (fun y => q y • φ y) x‖ ≤
      S * L * (C * Γ * (h ^ (n + 2))⁻¹ * Real.exp (-J / h)) :=
    hprod.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsum hL) hM)
  have hpow : h ^ n * (h ^ (n + 2))⁻¹ = (h ^ 2)⁻¹ := by
    rw [pow_add]
    field_simp
  calc
    _ ≤ Real.exp (w / h) * h ^ n *
        (S * L * (C * Γ * (h ^ (n + 2))⁻¹ * Real.exp (-J / h))) :=
      mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = (S * C * Γ * (h ^ n * (h ^ (n + 2))⁻¹)) *
        (Real.exp (w / h) * L * Real.exp (-J / h)) := by ring
    _ = (S * C * Γ * (h ^ 2)⁻¹) *
        (Real.exp (w / h) * L * Real.exp (-J / h)) := by rw [hpow]
    _ ≤ (S * C * Γ * (h ^ 2)⁻¹) * (Real.exp (-J₀ / h) * G) :=
      mul_le_mul_of_nonneg_left hgain (by positivity)
    _ = _ := by ring

/-- All semiclassical jets of the actual forcing have a uniform fine bound.
The constants precede the energy, weight strength, exterior coefficient and
wavefunction. The weight is applied after differentiation. -/
theorem exists_cusp_fine_forcing_jet_bound {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) (hgap : β₁ < p.β) (n : ℕ) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
      ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction, ContDiff ℝ ∞ φ →
      (∀ x, p.r₀ < ‖x‖ → φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ)) →
      ∀ x, Real.exp (κ / h * χ.weight x) * h ^ n *
        ‖iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ ≤
          C * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
            Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) := by
  let β₂ := (p.β + β₁) / 2
  have hβ₂ : 0 < β₂ := by dsimp [β₂]; linarith
  have h₁₂ : β₁ < β₂ := by dsimp [β₂]; linarith
  have h₂β : β₂ < p.β := by dsimp [β₂]; linarith
  choose A hA hAbound using fun i => exists_cuspPlus_jet_margin_bound hp hβ₂ h₂β i
  choose B hB hBbound using fun i => exists_cuspMinus_jet_margin_bound hp hβ₂ h₂β i
  let S (F : ℕ → ℝ) : ℝ :=
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * F i) + 1
  have hS (F : ℕ → ℝ) (hF : ∀ i, 0 < F i) : 0 < S F := by
    have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * F i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hF i).le
    dsimp [S]
    linarith
  have hSA := hS A hA
  have hSB := hS B hB
  have hr : p.r₀ < p.R := by linarith [hp.radius_large, hp.r₀_pos]
  obtain ⟨Cφ, hCφ, h₀, hh₀, hkernel⟩ := exists_uniform_exterior_landau_jet_bound
    hp.b_pos (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hp.r₀_pos.le hr (le_max_left p.R p.cuspSupportRadius) n
  refine ⟨p.ε * (S A + S B) * Cφ, mul_pos (mul_pos hp.ε_pos (add_pos hSA hSB)) hCφ, ?_⟩
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < h₀ :=
    (eventually_lt_nhds hh₀).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_logFlat_weighted_action_le hβ₁ h₁₂ (hp.t₀_pos.trans hp.t₀_lt)
      (show (0 : ℝ) < 1 / 16 by norm_num)] with h hh hsmall hlog
  have hhp : 0 < h := hh
  intro E hE κ hκ Γ hΓ φ hφ htail
  have hcomponent (q : Potential) (t : Plane → ℝ) (hq : ContDiff ℝ ∞ q)
      (F : ℕ → ℝ) (hF : ∀ i, 0 < F i)
      (hqbound : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ F i * logFlat β₂ p.tStar (t x))
      (hdata : ∀ x ∈ tsupport q, 0 ≤ t x ∧
        ‖x‖ ∈ Icc p.R (max p.R p.cuspSupportRadius) ∧
        κ * χ.weight x - (bridgeAction p.b E ‖x‖ - bridgeAction p.b E p.R) ≤
          -(1 / 16 : ℝ) * t x) :
      ∀ x, Real.exp (κ / h * χ.weight x) * h ^ n *
        ‖iteratedFDeriv ℝ n (fun y => q y • φ y) x‖ ≤
          S F * Cφ * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
            Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) := by
    intro x
    by_cases hx : x ∈ tsupport q
    · obtain ⟨ht, hxrad, hgain⟩ := hdata x hx
      have hweighted := hlog (t x) ht (κ * χ.weight x)
        (bridgeAction p.b E ‖x‖) (bridgeAction p.b E p.R) hgain
      have hbound := weighted_jet_smul_le_of_bounds hq hφ n x F (fun i => (hF i).le)
        hhp hCφ.le hΓ (logFlat_nonneg _ _ _) (hS F hF).le
        (show (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * F i) ≤ S F by
          dsimp [S]; linarith)
        (fun i _ => hqbound i x)
        (hkernel E hE h hhp hsmall.le Γ hΓ φ htail x hxrad) hweighted
      have harg : κ / h * χ.weight x = (κ * χ.weight x) / h := by ring
      simpa only [harg] using hbound
    · rw [cusp_product_jet_zero_off_tsupport hx n, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg (hS F hF).le hCφ.le) hΓ) (inv_nonneg.mpr (sq_nonneg h)))
          (Real.exp_pos _).le) (Real.exp_pos _).le
  have hplus := hcomponent p.cuspPlus p.normalCoordinate (cuspPlus_contDiff hp) A hA
    hAbound (fun x hx => by
      have hrad := cuspPlus_tsupport_norm_bounds hp hx
      refine ⟨(cuspPlus_tsupport_subset_quadratic p hx).1,
        ⟨hrad.1, hrad.2.trans (le_max_right _ _)⟩, ?_⟩
      convert χ.cuspPlus_weighted_action_gain hp hE hκ hx using 1
      ring)
  have hminus := hcomponent p.cuspMinus (fun x => p.normalCoordinate (reflection x))
    (cuspMinus_contDiff hp) B hB hBbound (fun x hx => by
      have href : reflection x ∈ tsupport p.cuspPlus :=
        tsupport_comp_subset_preimage p.cuspPlus reflection_contDiff.continuous hx
      have hrad := cuspMinus_tsupport_norm_bounds hp hx
      refine ⟨(cuspPlus_tsupport_subset_quadratic p href).1,
        ⟨hrad.1, hrad.2.trans (le_max_right _ _)⟩, ?_⟩
      convert χ.cuspMinus_weighted_action_gain hp hE hκ hx using 1
      ring)
  intro x
  calc
    _ ≤ Real.exp (κ / h * χ.weight x) * h ^ n *
        (p.ε * (‖iteratedFDeriv ℝ n (fun y => p.cuspPlus y • φ y) x‖ +
          ‖iteratedFDeriv ℝ n (fun y => p.cuspMinus y • φ y) x‖)) :=
      mul_le_mul_of_nonneg_left (norm_atomicPerturbation_product_jet_le hp hφ n x)
        (by positivity)
    _ = p.ε * (Real.exp (κ / h * χ.weight x) * h ^ n *
        ‖iteratedFDeriv ℝ n (fun y => p.cuspPlus y • φ y) x‖ +
      Real.exp (κ / h * χ.weight x) * h ^ n *
        ‖iteratedFDeriv ℝ n (fun y => p.cuspMinus y • φ y) x‖) := by ring
    _ ≤ p.ε * ((S A * Cφ * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
        Real.exp (-β₁ * (Real.log (1 / h)) ^ 2)) +
      (S B * Cφ * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
        Real.exp (-β₁ * (Real.log (1 / h)) ^ 2))) :=
      mul_le_mul_of_nonneg_left (add_le_add (hplus x) (hminus x)) hp.ε_pos.le
    _ = _ := by ring

end InfiniteZero.CuspParameters
