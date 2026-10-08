import InfiniteZero.AtomicCuspSource
import InfiniteZero.ConstructionCuspJetBounds
import InfiniteZero.CuspWeightedActionGain
import InfiniteZero.ExteriorRadialJetBounds
import InfiniteZero.WeightedSemiclassicalProduct

/-!
# Local jets of the genuine incoming cusp source

The exact exterior radial tail supplies the Landau action. On either closed
cusp support its radial gain is at least the normal coordinate divided by
eight. Leibniz retains the local log-flat profile, with any fixed strict
loss in its exponent. The polynomial power is deliberately nonoptimal;
the true source, its normalization and its full action are unchanged.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1200000

/-- Both closed cusp supports, including the tips, have the same uniform
incoming-source jet bound. The polynomial loss is `h^(-(n+4))`; this does
not claim the leading `h^(-7/2)` prefactor of the incoming expansion. -/
theorem exists_cusp_incoming_source_jet_bound
    {p : CuspParameters} (hp : p.BasicConditions) {βin : ℝ}
    (hβin : 0 < βin) (hβinβ : βin < p.β) (n : ℕ) :
    ∃ C > 0, ∃ h₀ > 0, ∀ E ∈ Icc (1 / 2 : ℝ) 1,
      ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ c : ℝ, 0 ≤ c → ∀ Γ : ℝ, 0 ≤ Γ →
      ∀ φ : Wavefunction, ContDiff ℝ ∞ φ →
      (∀ x : Plane, p.r₀ < ‖x‖ → φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ)) →
      ∀ j : ℕ, j ≤ n →
        (∀ x ∈ tsupport p.cuspPlus,
          h ^ j * ‖iteratedFDeriv ℝ j
            (atomicSource h p.atomicPerturbation (fun y => (c : ℂ) * φ y)) x‖ ≤
            C * c * Γ * (h ^ (n + 4))⁻¹ *
              logFlat βin p.tStar (p.normalCoordinate x) *
              Real.exp (-(bridgeAction p.b E p.R + p.normalCoordinate x / 8) / h)) ∧
        (∀ x ∈ tsupport p.cuspMinus,
          h ^ j * ‖iteratedFDeriv ℝ j
            (atomicSource h p.atomicPerturbation (fun y => (c : ℂ) * φ y)) x‖ ≤
            C * c * Γ * (h ^ (n + 4))⁻¹ *
              logFlat βin p.tStar (p.normalCoordinate (reflection x)) *
              Real.exp (-(bridgeAction p.b E p.R +
                p.normalCoordinate (reflection x) / 8) / h)) := by
  choose A hA hAbound using fun i => exists_cuspPlus_jet_margin_bound hp hβin hβinβ i
  choose B hB hBbound using fun i => exists_cuspMinus_jet_margin_bound hp hβin hβinβ i
  obtain ⟨Sp, hSp, hplusProduct⟩ := exists_weighted_semiclassical_smul_bound_upTo
    (E := Plane) (F := ℂ) n A (fun i _ => (hA i).le)
  obtain ⟨Sm, hSm, hminusProduct⟩ := exists_weighted_semiclassical_smul_bound_upTo
    (E := Plane) (F := ℂ) n B (fun i _ => (hB i).le)
  obtain ⟨CK, hCK, hK, hhK, hkernel⟩ := exists_uniform_exterior_landau_jet_bound
    hp.b_pos (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hp.r₀_pos.le (show p.r₀ < p.R by linarith [hp.radius_large, hp.r₀_pos])
    (le_max_left p.R p.cuspSupportRadius) n
  let C : ℝ := p.ε * (Sp + Sm) * CK
  have hC : 0 < C := mul_pos (mul_pos hp.ε_pos (add_pos hSp hSm)) hCK
  refine ⟨C, hC, min hK 1, lt_min hhK zero_lt_one, ?_⟩
  intro E hE h hh hsmall c hc Γ hΓ φ hφ htail j hj
  have hh1 : h ≤ 1 := hsmall.trans (min_le_right _ _)
  have hhK' : h ≤ hK := hsmall.trans (min_le_left _ _)
  let u : Wavefunction := fun x => (c : ℂ) * φ x
  have hu : ContDiff ℝ ∞ u := contDiff_const.mul hφ
  have htailu : ∀ x : Plane, p.r₀ < ‖x‖ →
      u x = (((c * Γ : ℝ) : ℂ) * (landauKernel p.b h E ‖x‖ : ℂ)) := by
    intro x hx
    dsimp [u]
    rw [htail x hx]
    push_cast
    ring
  have hpow : (h ^ 2)⁻¹ * (h ^ (n + 2))⁻¹ = (h ^ (n + 4))⁻¹ := by
    rw [← mul_inv, ← pow_add]
    congr 2
    omega
  have hcomponent (q : Potential) (t : Plane → ℝ) (S : ℝ)
      (hS : 0 ≤ S) (hSsum : S ≤ Sp + Sm)
      (_hq : ContDiff ℝ ∞ q) (D : ℕ → ℝ)
      (hqbound : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ D i * logFlat βin p.tStar (t x))
      (hproduct : ∀ x : Plane, ∀ L M : ℝ, 0 ≤ L → 0 ≤ M →
        (∀ i ≤ n, ‖iteratedFDeriv ℝ i q x‖ ≤ D i * L) →
        (∀ k ≤ n, h ^ k * ‖iteratedFDeriv ℝ k u x‖ ≤ M) →
        h ^ j * ‖iteratedFDeriv ℝ j (fun y => q y • u y) x‖ ≤ S * L * M)
      (x : Plane) (hxrad : ‖x‖ ∈ Icc p.R p.cuspSupportRadius)
      (hgain : bridgeAction p.b E p.R + t x / 8 ≤ bridgeAction p.b E ‖x‖)
      (hsource : ‖iteratedFDeriv ℝ j (atomicSource h p.atomicPerturbation u) x‖ =
        ((h ^ 2)⁻¹ * p.ε) *
          ‖iteratedFDeriv ℝ j (fun y => q y • u y) x‖) :
      h ^ j * ‖iteratedFDeriv ℝ j (atomicSource h p.atomicPerturbation u) x‖ ≤
        C * c * Γ * (h ^ (n + 4))⁻¹ * logFlat βin p.tStar (t x) *
          Real.exp (-(bridgeAction p.b E p.R + t x / 8) / h) := by
    let M : ℝ := CK * (c * Γ) * (h ^ (n + 2))⁻¹ *
      Real.exp (-bridgeAction p.b E ‖x‖ / h)
    have hε : 0 ≤ p.ε := hp.ε_pos.le
    have hL : 0 ≤ logFlat βin p.tStar (t x) := logFlat_nonneg _ _ _
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hubound (k : ℕ) (hk : k ≤ n) :
        h ^ k * ‖iteratedFDeriv ℝ k u x‖ ≤ M := by
      calc
        _ ≤ 1 * ‖iteratedFDeriv ℝ k u x‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hh.le hh1) (norm_nonneg _)
        _ ≤ M := by
          simpa only [one_mul, M] using
            hkernel E hE h hh hhK' (c * Γ) (mul_nonneg hc hΓ) u htailu x
              ⟨hxrad.1, hxrad.2.trans (le_max_right _ _)⟩ k hk
    have hprod := hproduct x (logFlat βin p.tStar (t x)) M
      (logFlat_nonneg _ _ _) hM (fun i _ => hqbound i x) hubound
    have hexp : Real.exp (-bridgeAction p.b E ‖x‖ / h) ≤
        Real.exp (-(bridgeAction p.b E p.R + t x / 8) / h) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hgain) hh.le)
    calc
      _ = ((h ^ 2)⁻¹ * p.ε) *
          (h ^ j * ‖iteratedFDeriv ℝ j (fun y => q y • u y) x‖) := by rw [hsource]; ring
      _ ≤ ((h ^ 2)⁻¹ * p.ε) * (S * logFlat βin p.tStar (t x) * M) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (p.ε * S * CK) * c * Γ * (h ^ (n + 4))⁻¹ *
          logFlat βin p.tStar (t x) * Real.exp (-bridgeAction p.b E ‖x‖ / h) := by
        dsimp [M]
        calc
          _ = (p.ε * S * CK) * c * Γ * ((h ^ 2)⁻¹ * (h ^ (n + 2))⁻¹) *
              logFlat βin p.tStar (t x) * Real.exp (-bridgeAction p.b E ‖x‖ / h) := by ring
          _ = _ := by rw [hpow]
      _ ≤ (p.ε * S * CK) * c * Γ * (h ^ (n + 4))⁻¹ *
          logFlat βin p.tStar (t x) *
            Real.exp (-(bridgeAction p.b E p.R + t x / 8) / h) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ _ := by
        dsimp [C]
        gcongr
  constructor
  · intro x hx
    refine hcomponent p.cuspPlus p.normalCoordinate Sp hSp.le
      (le_add_of_nonneg_right hSm.le) (cuspPlus_contDiff hp) A hAbound ?_ x
      (cuspPlus_tsupport_norm_bounds hp hx)
      (cuspPlus_tsupport_action_gain_eighth hp hE hx) ?_
    · intro y L M hL hM hqbound hubound
      simpa only [one_mul] using hplusProduct p.cuspPlus u (cuspPlus_contDiff hp)
        hu y h 1 L M hh.le hh1 zero_le_one hL hM hqbound
          (by simpa only [one_mul] using hubound) j hj
    · rw [iteratedFDeriv_atomicPerturbation_source_eq_plus hp h u hx j]
      exact norm_iteratedFDeriv_componentSource_plus hp hu h j x
  · intro x hx
    refine hcomponent p.cuspMinus (fun y => p.normalCoordinate (reflection y)) Sm hSm.le
      (le_add_of_nonneg_left hSp.le) (cuspMinus_contDiff hp) B hBbound ?_ x
      (cuspMinus_tsupport_norm_bounds hp hx)
      (cuspMinus_tsupport_action_gain_eighth hp hE hx) ?_
    · intro y L M hL hM hqbound hubound
      simpa only [one_mul] using hminusProduct p.cuspMinus u (cuspMinus_contDiff hp)
        hu y h 1 L M hh.le hh1 zero_le_one hL hM hqbound
          (by simpa only [one_mul] using hubound) j hj
    · rw [iteratedFDeriv_atomicPerturbation_source_eq_minus hp h u hx j]
      exact norm_iteratedFDeriv_componentSource_minus hp hu h j x

end InfiniteZero.CuspParameters
