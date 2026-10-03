import InfiniteZero.ActiveCrossPairingBound

/-!
# Combining two source L¹ bounds without losing the active action

The two radial source actions and the bridge action combine into the exact
`activeReferenceAction`. Polynomial exponents and logarithmic costs add.
The same constant covers both ordered active cusp pairs, and is fixed
before every source, scale, amplitude, exponent, and energy.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem exists_activeSourcePairing_L1_bound {p : CuspParameters}
    (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    ∃ K > 0, ∀ coupling : ℝ, 1 ≤ coupling → ∀ E ∈ Icc (1 / 2 : ℝ) 1,
      ∀ E₀ c Γ CF CG β₁ β₂ : ℝ, 0 ≤ c → 0 ≤ Γ → 0 ≤ CF → 0 ≤ CG →
      ∀ N M : ℕ, ∀ F G : Wavefunction, Integrable F → Integrable G →
      ((Function.support F ⊆ tsupport p.cuspPlus ∧
          Function.support G ⊆ tsupport p.cuspMinus) ∨
        (Function.support F ⊆ tsupport p.cuspMinus ∧
          Function.support G ⊆ tsupport p.cuspPlus)) →
      (∫ z : Plane, ‖F z‖) ≤ CF * coupling ^ N *
        (c * Γ * Real.exp (-coupling * bridgeAction p.b E₀ p.R)) *
          Real.exp (-β₁ * (Real.log coupling) ^ 2) →
      (∫ w : Plane, ‖G w‖) ≤ CG * coupling ^ M *
        (c * Γ * Real.exp (-coupling * bridgeAction p.b E₀ p.R)) *
          Real.exp (-β₂ * (Real.log coupling) ^ 2) →
      ‖sourcePairing coupling⁻¹ (sourceKernel p.b L coupling⁻¹ E) F G‖ ≤
        K * CF * CG * c ^ 2 * Γ ^ 2 * coupling ^ (N + M) *
          Real.exp (-coupling * p.activeReferenceAction L E E₀) *
            Real.exp (-(β₁ + β₂) * (Real.log coupling) ^ 2) := by
  obtain ⟨K, hK, hpair⟩ := exists_activeCrossPairing_exact_action_bound hp hL
  refine ⟨K, hK, ?_⟩
  intro coupling hc1 E hE E₀ c Γ CF CG β₁ β₂ hc hΓ hCF hCG N M F G hF hG hsupport hFB hGB
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hcpos
  have hh1 : coupling⁻¹ ≤ 1 := (inv_le_one₀ hcpos).mpr hc1
  have haction :
      Real.exp (-bridgeAction p.b E (Geometry.activeDistance p.R L) / coupling⁻¹) *
          Real.exp (-coupling * bridgeAction p.b E₀ p.R) *
          Real.exp (-coupling * bridgeAction p.b E₀ p.R) =
        Real.exp (-coupling * p.activeReferenceAction L E E₀) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [div_inv_eq_mul, activeReferenceAction]
    ring
  have hlog : Real.exp (-β₁ * (Real.log coupling) ^ 2) *
        Real.exp (-β₂ * (Real.log coupling) ^ 2) =
      Real.exp (-(β₁ + β₂) * (Real.log coupling) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ K * Real.exp (-bridgeAction p.b E (Geometry.activeDistance p.R L) / coupling⁻¹) *
        (∫ z : Plane, ‖F z‖) * (∫ w : Plane, ‖G w‖) :=
      hpair E hE coupling⁻¹ hh hh1 F G hF hG hsupport
    _ ≤ K * Real.exp (-bridgeAction p.b E (Geometry.activeDistance p.R L) / coupling⁻¹) *
        (CF * coupling ^ N * (c * Γ * Real.exp (-coupling * bridgeAction p.b E₀ p.R)) *
          Real.exp (-β₁ * (Real.log coupling) ^ 2)) *
        (CG * coupling ^ M * (c * Γ * Real.exp (-coupling * bridgeAction p.b E₀ p.R)) *
          Real.exp (-β₂ * (Real.log coupling) ^ 2)) := by
      gcongr
    _ = K * CF * CG * c ^ 2 * Γ ^ 2 * (coupling ^ N * coupling ^ M) *
        (Real.exp (-bridgeAction p.b E (Geometry.activeDistance p.R L) / coupling⁻¹) *
          Real.exp (-coupling * bridgeAction p.b E₀ p.R) *
          Real.exp (-coupling * bridgeAction p.b E₀ p.R)) *
        (Real.exp (-β₁ * (Real.log coupling) ^ 2) *
          Real.exp (-β₂ * (Real.log coupling) ^ 2)) := by ring
    _ = _ := by rw [← pow_add, haction, hlog]

end InfiniteZero.CuspParameters
