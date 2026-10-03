import InfiniteZero.AtomicComponentSourceL1
import InfiniteZero.InactiveCellL1Bounds
import InfiniteZero.RadialCoreEnergyBounds
import InfiniteZero.SourcePhaseInvariance

/-!
# The seven inactive cells of the genuine constructed atomic state

The fixed potential and separation certificate precede the separation,
constants and coupling. The same positive radial reference state and its
exact exterior coefficient supply all source estimates. The bridge uses
the full atomic energy; the radial actions use the core energy. Simplicity
then transfers the seven cell bounds to the canonical full atomic state.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem exists_atomicGround_inactive_cells_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
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
          (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ∈
            Icc (1 / 2 : ℝ) 1 ∧
          ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
            let B := C * (Γ ^ 2 + 1) * coupling ^ 10 *
              Real.exp (-coupling * (p.activeReferenceAction L (scaledAtomicEnergy p coupling)
                (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) +
                  31 * p.hopMargin))
            ‖sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ i j‖ ≤ B ∧
              ‖canonicalSourceCell p L coupling i j‖ ≤ B := by
  have hβ : 0 < p.β / 2 := half_pos hp.β_pos
  have hββ : p.β / 2 < p.β := by linarith [hp.β_pos]
  obtain ⟨S, hS, Ts, _hTs, hstates⟩ :=
    exists_atomicGround_component_source_L1_of_radialData
      hInterior hp hRad hAcore hApot χ hβ hββ
  obtain ⟨Te, _hTe, henergy⟩ :=
    exists_scaledAtomicEnergy_pos_of_radialData hp hRad hAcore hApot
  obtain ⟨Tr, _hTr, hradialEnergy⟩ :=
    exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  obtain ⟨Tg, _hTg, hground⟩ :=
    eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  obtain ⟨K, hK, hcell⟩ := exists_inactiveCell_L1_bound hp cert hL
  let C := K * (coreSourceConstant p + S + 1) ^ 2
  have hC : 0 < C := by
    have hcore := coreSourceConstant_pos p
    dsimp [C]
    positivity
  let threshold := max Ts (max Te (max Tr (max Tg 1)))
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact zero_lt_one.trans_le
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨C, hC, threshold, hthreshold, ?_⟩
  intro coupling hc
  have hthresholds : Ts ≤ coupling ∧ Te ≤ coupling ∧ Tr ≤ coupling ∧
      Tg ≤ coupling ∧ 1 ≤ coupling := by
    simpa only [threshold, max_le_iff] using hc
  obtain ⟨hcTs, hcTe, hcTr, hcTg, hc1⟩ := hthresholds
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    _hInt, _hcore, hsum⟩ := hstates coupling hcTs
  have hE := henergy coupling hcTe
  have hEr := hradialEnergy coupling hcTr
  have hEbox : scaledAtomicEnergy p coupling ∈ Icc (1 / 2 : ℝ) 1 := ⟨hE.1, hE.2.2⟩
  have hErbox : -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling) ∈
      Ioc (0 : ℝ) 2 := ⟨by linarith [hEr.1], by linarith [hEr.2]⟩
  let B := S * Γ * coupling ^ 6 * Real.exp (-coupling * bridgeAction p.b
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hexp : Real.exp (-(p.β / 2) * (Real.log coupling) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (sq_nonneg _)
  have hdrop : B * Real.exp (-(p.β / 2) * (Real.log coupling) ^ 2) ≤ B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hB
  have hsource (i : Fin 3) (hi : i = 1 ∨ i = 2) :
      (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ i x‖) ≤ B := by
    have hsum' : (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 1 x‖) +
        (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 2 x‖) ≤ B := hsum.trans hdrop
    have hn₁ : 0 ≤ ∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 1 x‖ :=
      integral_nonneg (fun _ => norm_nonneg _)
    have hn₂ : 0 ≤ ∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 2 x‖ :=
      integral_nonneg (fun _ => norm_nonneg _)
    rcases hi with rfl | rfl
    · exact (le_add_of_nonneg_right hn₂).trans hsum'
    · exact (le_add_of_nonneg_left hn₁).trans hsum'
  have hcells := hcell coupling hc1 _ hEbox _ hErbox Γ hΓ.le S hS.le ψ hψ hsource
  have hsimple := (hground coupling hcTg).2.1
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail, hEbox, hEr, ?_⟩
  intro i j hij₁ hij₂
  have hb := hcells i j hij₁ hij₂
  refine ⟨hb, ?_⟩
  rw [canonicalSourceCell_eq_sourceCell p L coupling hsimple ψ hψ i j]
  exact hb

end InfiniteZero.CuspParameters
