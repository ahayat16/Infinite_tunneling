import InfiniteZero.RadialCoreNormalizationLower

/-!
# Polynomial control of the relative normalization quotient

The reciprocal estimate for the very same exterior coefficient absorbs
`(Γ² + 1) / Γ²`, and a Schur normalization at least one half costs at
most four more. No state or coefficient is chosen independently.
-/

noncomputable section
open Set

namespace InfiniteZero

/-- The lower bound for Γ turns the relative normalization quotient into
a fixed polynomial loss. -/
theorem normalizationRatio_le {Γ coupling C : ℝ}
    (hΓ : 0 < Γ) (hcoupling : 1 ≤ coupling) (_hC : 0 ≤ C)
    (hinv : Γ⁻¹ ≤ C * coupling ^ 2) :
    (Γ ^ 2 + 1) / Γ ^ 2 ≤ (1 + C ^ 2) * coupling ^ 4 := by
  have hsq : (Γ⁻¹) ^ 2 ≤ C ^ 2 * coupling ^ 4 := by
    calc
      _ ≤ (C * coupling ^ 2) ^ 2 := pow_le_pow_left₀ (inv_pos.mpr hΓ).le hinv 2
      _ = _ := by ring
  have hfour : 1 ≤ coupling ^ 4 := one_le_pow₀ hcoupling
  calc
    _ = 1 + (Γ⁻¹) ^ 2 := by field_simp [hΓ.ne']
    _ ≤ coupling ^ 4 + C ^ 2 * coupling ^ 4 := add_le_add hfour hsq
    _ = _ := by ring

/-- A normalization `c ≥ 1/2` costs at most the factor four, uniformly in c. -/
theorem normalizationRatio_div_schur_le {Γ coupling C c : ℝ}
    (hΓ : 0 < Γ) (hcoupling : 1 ≤ coupling) (hC : 0 ≤ C)
    (hinv : Γ⁻¹ ≤ C * coupling ^ 2) (hc : (1 / 2 : ℝ) ≤ c) :
    (Γ ^ 2 + 1) / (c ^ 2 * Γ ^ 2) ≤ 4 * (1 + C ^ 2) * coupling ^ 4 := by
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hcinv : c⁻¹ ≤ 2 := by
    simpa only [one_div] using
      (div_le_iff₀ hcpos).mpr (by linarith : (1 : ℝ) ≤ 2 * c)
  have hcsq : (c⁻¹) ^ 2 ≤ 4 := by
    have hh := pow_le_pow_left₀ (inv_pos.mpr hcpos).le hcinv 2
    norm_num at hh ⊢
    exact hh
  have hq := normalizationRatio_le hΓ hcoupling hC hinv
  calc
    _ = (c⁻¹) ^ 2 * ((Γ ^ 2 + 1) / Γ ^ 2) := by
      field_simp [hΓ.ne', hcpos.ne']
    _ ≤ 4 * ((1 + C ^ 2) * coupling ^ 4) :=
      mul_le_mul hcsq hq (by positivity) (by norm_num)
    _ = _ := by ring

namespace CuspParameters

/-- Uniform relative bounds for every positive radial core ground state and
every coefficient representing its own exact tail. The constants precede
the coupling, state, coefficient and Schur normalization. -/
theorem exists_radialCore_normalizationRatio_bound_of_radialData
    {p : CuspParameters} {b : ℝ} (hb : 0 < b) (hr : 0 < p.r₀)
    (hRad : RadialCoreSpectralData b p)
    (hAcore : ∀ coupling, IsMagneticRealization b coupling p.core) :
    ∃ D > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ → IsPositiveRadial φ →
        ∀ Γ : ℝ,
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ)) →
          0 < Γ ∧ (Γ ^ 2 + 1) / Γ ^ 2 ≤ D * coupling ^ 4 ∧
            ∀ c : ℝ, (1 / 2 : ℝ) ≤ c →
              (Γ ^ 2 + 1) / (c ^ 2 * Γ ^ 2) ≤ 4 * D * coupling ^ 4 := by
  obtain ⟨_c₀, _hc₀, C, hC, T, _hT, hbounds⟩ :=
    exists_radialCore_coefficient_bounds_of_radialData hb hr hRad hAcore
  refine ⟨1 + C ^ 2, by positivity, max T 1,
    zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hcoupling φ hφ hpos Γ htail
  have hT' : T ≤ coupling := (le_max_left _ _).trans hcoupling
  have hc1 : 1 ≤ coupling := (le_max_right _ _).trans hcoupling
  obtain ⟨hΓ, _hlower, hinv⟩ := hbounds coupling hT' φ hφ hpos Γ htail
  exact ⟨hΓ, normalizationRatio_le hΓ hc1 hC.le hinv,
    fun c hc => normalizationRatio_div_schur_le hΓ hc1 hC.le hinv hc⟩

end CuspParameters
end InfiniteZero
