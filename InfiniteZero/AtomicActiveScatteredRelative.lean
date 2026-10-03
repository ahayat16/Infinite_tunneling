import InfiniteZero.AtomicActiveScatteredBounds
import InfiniteZero.ActiveScatteredEnvelope
import InfiniteZero.SourcePairingAdditivity
import InfiniteZero.SourcePhaseInvariance

/-!
# Removing the actual scattered response from the active cell

The same true atomic state, positive radial reference, Schur coefficient
and exact exterior coefficient are retained throughout. The three terms
containing the response are negligible relative to the literal manuscript
envelope whenever `3β₀ > 2β`. This proves a reduction to the incoming cell;
it does not assume or assert its stationary-phase asymptotic.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

theorem scattered_three_norms_le {coupling β₀ Cmix Css B : ℝ}
    (hcoupling : 1 ≤ coupling) (hβ₀ : 0 ≤ β₀) (hCm : 0 ≤ Cmix) (hCs : 0 ≤ Css) (hB : 0 ≤ B)
    {a b d : ℂ}
    (ha : ‖a‖ ≤ Cmix * B * coupling ^ 10 * Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2))
    (hb : ‖b‖ ≤ Cmix * B * coupling ^ 10 * Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2))
    (hd : ‖d‖ ≤ Css * B * coupling ^ 12 * Real.exp (-(4 * β₀) * (Real.log coupling) ^ 2)) :
    ‖a‖ + ‖b‖ + ‖d‖ ≤
      (2 * Cmix + Css) * (B * coupling ^ 12 * Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2)) := by
  have hcouplingpos : 0 ≤ coupling := zero_le_one.trans hcoupling
  have hpow : coupling ^ 10 ≤ coupling ^ 12 := pow_le_pow_right₀ hcoupling (by norm_num)
  have hexp : Real.exp (-(4 * β₀) * (Real.log coupling) ^ 2) ≤
      Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hβ₀ (sq_nonneg (Real.log coupling))]
  have hm : Cmix * B * coupling ^ 10 * Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2) ≤
      Cmix * B * coupling ^ 12 * Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2) := by gcongr
  have hs : Css * B * coupling ^ 12 * Real.exp (-(4 * β₀) * (Real.log coupling) ^ 2) ≤
      Css * B * coupling ^ 12 * Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2) := by gcongr
  nlinarith only [ha.trans hm, hb.trans hm, hd.trans hs]

namespace CuspParameters

theorem exists_atomicGround_active_scattered_relative_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {L β₀ : ℝ} (hL : p.R < 2 * L)
    (hβ₀ : 0 < β₀) (hβ₀β : β₀ < p.β) (hmargin : 2 * p.β < 3 * β₀) :
    ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          scaledAtomicEnergy p coupling ∈ Icc (1 / 2 : ℝ) 1 ∧
          let u : Wavefunction := fun x => (c : ℂ) * φ x
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let R := C * p.activeSaddleTexEnvelope L coupling c Γ *
            Real.exp (-((3 * β₀ - 2 * p.β) / 2) * (Real.log coupling) ^ 2)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          0 < p.activeSaddleTexEnvelope L coupling c Γ ∧
          ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ 1 2 -
            sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2‖ ≤ R ∧
          ‖canonicalSourceCell p L coupling 1 2 -
            sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2‖ ≤ R := by
  obtain ⟨Cm, hCm, Cs, hCs, Ts, _hTs, hstates⟩ :=
    exists_atomicGround_active_scattered_bounds_of_radialData
      hInterior hp hRad hAcore hApot χ hL hβ₀ hβ₀β
  obtain ⟨Tr, _hTr, hrelative⟩ :=
    exists_logarithmicBound_le_activeSaddleTexEnvelope hp L hmargin 12
  obtain ⟨Tg, _hTg, hground⟩ :=
    eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  let C := (2 * Cm + Cs) * (2 / (p.ε ^ 2 * p.a ^ 2))
  have hC : 0 < C := by
    have hε := hp.ε_pos
    have ha := hp.a_pos
    dsimp [C]
    positivity
  let threshold := max Ts (max Tr (max Tg 1))
  have hthreshold : 0 < threshold := zero_lt_one.trans_le
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C, hC, threshold, hthreshold, ?_⟩
  intro coupling hc
  have hthresholds : Ts ≤ coupling ∧ Tr ≤ coupling ∧ Tg ≤ coupling ∧ 1 ≤ coupling := by
    simpa only [threshold, max_le_iff] using hc
  obtain ⟨hcTs, hcTr, hcTg, hc1⟩ := hthresholds
  have hcoupling : 0 < coupling := zero_lt_one.trans_le hc1
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail, hEbox,
    hηsmooth, hηLp, horth, hmix₁, hmix₂, hss⟩ := hstates coupling hcTs
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hcRange.1
  obtain ⟨henv, hbound⟩ := hrelative coupling hcTr c Γ hcpos hΓ
  let u : Wavefunction := fun x => (c : ℂ) * φ x
  let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
  let Q := fun f g : Wavefunction => sourcePairing coupling⁻¹
    (sourceKernel p.b L coupling⁻¹ (scaledAtomicEnergy p coupling))
      (componentSource p coupling⁻¹ f 1) (componentSource p coupling⁻¹ g 2)
  let B := c ^ 2 * Γ ^ 2 * Real.exp (-coupling *
    (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsum := scattered_three_norms_le hc1 hβ₀.le hCm.le hCs.le hB hmix₁ hmix₂ hss
  have hnormsum : ‖Q u η‖ + ‖Q η u‖ + ‖Q η η‖ ≤
      C * p.activeSaddleTexEnvelope L coupling c Γ *
        Real.exp (-((3 * β₀ - 2 * p.β) / 2) * (Real.log coupling) ^ 2) := by
    calc
      _ ≤ (2 * Cm + Cs) * (B * coupling ^ 12 *
          Real.exp (-(3 * β₀) * (Real.log coupling) ^ 2)) := hsum
      _ ≤ (2 * Cm + Cs) * ((2 / (p.ε ^ 2 * p.a ^ 2)) *
          p.activeSaddleTexEnvelope L coupling c Γ *
          Real.exp (-((3 * β₀ - 2 * p.β) / 2) * (Real.log coupling) ^ 2)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by dsimp [C]; ring
  have hdecomp : ψ = u + η := by
    funext x
    simp [u, η]
  have hu : Continuous u := continuous_const.mul hφ.1.1.continuous
  have hEpos : 0 < scaledAtomicEnergy p coupling :=
    lt_of_lt_of_le (by norm_num) hEbox.1
  have hcell : sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ 1 2 -
      sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2 =
      Q u η + Q η u + Q η η := by
    rw [hdecomp, sourceCell_add_eq_four_pairings hp hL (inv_pos.mpr hcoupling)
      hEpos hu hηsmooth.continuous]
    change Q u u + Q u η + Q η u + Q η η - Q u u = _
    ring
  have hactual : ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ 1 2 -
      sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) u 1 2‖ ≤
      C * p.activeSaddleTexEnvelope L coupling c Γ *
        Real.exp (-((3 * β₀ - 2 * p.β) / 2) * (Real.log coupling) ^ 2) := by
    rw [hcell]
    exact (norm_add_le_of_le (norm_add_le _ _) le_rfl).trans hnormsum
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail, hEbox,
    hηsmooth, hηLp, horth, henv, hactual, ?_⟩
  rw [canonicalSourceCell_eq_sourceCell p L coupling (hground coupling hcTg).2.1 ψ hψ]
  exact hactual

end CuspParameters
end InfiniteZero
