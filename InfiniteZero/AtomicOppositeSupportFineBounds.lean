import InfiniteZero.OppositeSupportReconstruction
import InfiniteZero.UniversalComponentSourceL1
import InfiniteZero.RadialCoreNormalizationLower
import InfiniteZero.RadialCoreEnergyBounds
import InfiniteZero.AtomicSourceRegime

/-!
# Fine opposite-support masses from the actual component sources

The source constants and the reciprocal bound for the same exterior
coefficient are fixed before the coupling and all supplied ground states.
The radial source action and the full-state bridge action remain distinct.
-/

noncomputable section
open Set Filter MeasureTheory

namespace InfiniteZero

theorem oppositeSupport_source_envelope_le
    {coupling Γ c K C₀ Cs CΓ F₀ Fc G J β : ℝ}
    (hcoupling : 1 ≤ coupling) (hΓ : 0 < Γ) (hc : (1 / 2 : ℝ) ≤ c)
    (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hCs : 0 ≤ Cs) (hCΓ : 0 ≤ CΓ)
    (hinv : Γ⁻¹ ≤ CΓ * coupling ^ 2) (hβ : 0 ≤ β)
    (hF₀ : F₀ ≤ C₀ * coupling ^ 2)
    (hFc : Fc ≤ Cs * Γ * coupling ^ 6 * Real.exp (-coupling * G) *
      Real.exp (-β * (Real.log coupling) ^ 2)) :
    K * ((coupling⁻¹) ^ 2 * Real.exp (-coupling * (G + J)) * F₀ +
      Real.exp (-coupling * J) * Fc) ≤
      (2 * K * (C₀ * CΓ + Cs)) * (c * Γ) * coupling ^ 6 *
        Real.exp (-coupling * (G + J)) := by
  have hcp : 0 < coupling := zero_lt_one.trans_le hcoupling
  have hlog : Real.exp (-β * (Real.log coupling) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith only [mul_nonneg hβ (sq_nonneg (Real.log coupling))]
  have hFc' : Fc ≤ Cs * Γ * coupling ^ 6 * Real.exp (-coupling * G) :=
    hFc.trans (mul_le_of_le_one_right (by positivity) hlog)
  have hcore : (coupling⁻¹) ^ 2 * Real.exp (-coupling * (G + J)) * F₀ ≤
      C₀ * Real.exp (-coupling * (G + J)) := by
    calc
      _ ≤ (coupling⁻¹) ^ 2 * Real.exp (-coupling * (G + J)) *
          (C₀ * coupling ^ 2) :=
        mul_le_mul_of_nonneg_left hF₀ (by positivity)
      _ = _ := by field_simp
  have hcusp : Real.exp (-coupling * J) * Fc ≤
      Cs * Γ * coupling ^ 6 * Real.exp (-coupling * (G + J)) := by
    calc
      _ ≤ Real.exp (-coupling * J) *
          (Cs * Γ * coupling ^ 6 * Real.exp (-coupling * G)) :=
        mul_le_mul_of_nonneg_left hFc' (Real.exp_pos _).le
      _ = _ := by
        rw [show -coupling * (G + J) = -coupling * J + -coupling * G by ring,
          Real.exp_add]
        ring
  have hone : 1 ≤ Γ * CΓ * coupling ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hinv hΓ.le
    rw [mul_inv_cancel₀ hΓ.ne'] at h
    nlinarith only [h]
  have hp26 : coupling ^ 2 ≤ coupling ^ 6 :=
    pow_le_pow_right₀ hcoupling (by norm_num)
  have hone6 : 1 ≤ Γ * CΓ * coupling ^ 6 := hone.trans
    (mul_le_mul_of_nonneg_left hp26 (mul_nonneg hΓ.le hCΓ))
  have hC : C₀ ≤ C₀ * CΓ * Γ * coupling ^ 6 := by
    nlinarith only [mul_le_mul_of_nonneg_left hone6 hC₀]
  have hraw : K * ((coupling⁻¹) ^ 2 * Real.exp (-coupling * (G + J)) * F₀ +
      Real.exp (-coupling * J) * Fc) ≤
      K * (C₀ * CΓ + Cs) * Γ * coupling ^ 6 * Real.exp (-coupling * (G + J)) := by
    calc
      _ ≤ K * (C₀ * Real.exp (-coupling * (G + J)) +
          Cs * Γ * coupling ^ 6 * Real.exp (-coupling * (G + J))) :=
        mul_le_mul_of_nonneg_left (add_le_add hcore hcusp) hK
      _ ≤ K * ((C₀ * CΓ * Γ * coupling ^ 6) * Real.exp (-coupling * (G + J)) +
          Cs * Γ * coupling ^ 6 * Real.exp (-coupling * (G + J))) := by
        gcongr
      _ = _ := by ring
  apply hraw.trans
  have hc' : 1 ≤ 2 * c := by linarith
  have hm := mul_le_mul_of_nonneg_left hc'
    (show 0 ≤ K * (C₀ * CΓ + Cs) * Γ * coupling ^ 6 *
      Real.exp (-coupling * (G + J)) by positivity)
  nlinarith only [hm]

namespace CuspParameters

/-- Both opposite-potential integrals have the fine squared route action.
The defect has not yet been multiplied by λ², nor the residual mass by λ⁴.
The same supplied positive radial state fixes Γ in every occurrence. -/
theorem exists_atomic_oppositeSupport_mass_fine_bound_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hKernel : HasPositiveLandauResolvent p.b)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ C > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ → IsPositiveRadial φ →
      ∀ Γ : ℝ,
        (∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel p.b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) →
      ∀ c : ℝ, (1 / 2 : ℝ) ≤ c →
      ∀ ψ : Wavefunction, IsAtomicGroundState p.b p.potential coupling ψ →
        0 < Γ ∧
        let B := C * c ^ 2 * Γ ^ 2 * coupling ^ 12 * Real.exp (-2 * coupling *
          (bridgeAction p.b (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R +
            bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)))
        |∫ x : Plane, p.potential (x + displacement L) *
          ‖rightState p.b L coupling ψ x‖ ^ 2| ≤ B ∧
        mass (fun x => (p.potential (x + displacement L) : ℂ) *
          rightState p.b L coupling ψ x) ≤ B := by
  obtain ⟨Cs, hCs, Ts, _, hsource⟩ := exists_universal_component_source_L1_of_radialData
    hInterior hp hRad hAcore hApot χ
    (show 0 < p.β / 2 by linarith [hp.β_pos])
    (show p.β / 2 < p.β by linarith [hp.β_pos])
  obtain ⟨_cΓ, _hcΓ, CΓ, hCΓ, TΓ, _, hΓbound⟩ :=
    exists_radialCore_coefficient_bounds_of_radialData hp.b_pos hp.r₀_pos hRad hAcore
  obtain ⟨Tf, _, hEf⟩ := exists_scaledAtomicEnergy_pos_of_radialData hp hRad hAcore hApot
  obtain ⟨Tc, _, hEc⟩ := exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  obtain ⟨K, hK, hmass⟩ := exists_oppositeSupport_mass_bound_componentL1 hp cert hL
  let A := 2 * K * (coreSourceConstant p * CΓ + Cs)
  have hA : 0 < A := by
    have hC₀ := coreSourceConstant_pos p
    dsimp [A]
    positivity
  let Vnorm := ∫ x : Plane, |p.potential x|
  have hVnorm : 0 ≤ Vnorm := integral_nonneg fun x => abs_nonneg _
  let T := max 1 (max Ts (max TΓ (max Tf Tc)))
  refine ⟨A ^ 2 * (Vnorm + 1), by positivity,
    T, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc φ hφ hpos Γ htail c hcc ψ hψ
  have hc1 : 1 ≤ coupling := (le_max_left _ _).trans hc
  have hcs : Ts ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcg : TΓ ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hcf : Tf ≤ coupling := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hccore : Tc ≤ coupling := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  obtain ⟨hΓ, _, hinv⟩ := hΓbound coupling hcg φ hφ hpos Γ htail
  obtain ⟨_, hF₀, hFc⟩ := hsource coupling hcs φ hφ hpos Γ htail ψ hψ
  obtain ⟨hElow, hEp, hEup⟩ := hEf coupling hcf
  have hEc' := hEc coupling hccore
  have hcp := zero_lt_one.trans_le hc1
  have hR := rightResolventRepresentation_of_freeLandauResolventKernel
    (hKernel coupling (scaledAtomicEnergy p coupling) hcp hEp)
    (potential_contDiff hp) (potential_hasCompactSupport hp) hψ hcp rfl L
  have hraw := hmass coupling hc1 _ ⟨hElow, hEup⟩ _
    ⟨by linarith only [hEc'.1], hEc'.2.trans (by norm_num)⟩ ψ hψ.1.1.continuous hR
  let G := bridgeAction p.b
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R
  let J := bridgeAction p.b (scaledAtomicEnergy p coupling) (Geometry.activeDistance p.R L)
  let F₀ := ∫ z : Plane, ‖componentSource p coupling⁻¹ ψ 0 z‖
  let Fc := (∫ z : Plane, ‖componentSource p coupling⁻¹ ψ 1 z‖) +
    ∫ z : Plane, ‖componentSource p coupling⁻¹ ψ 2 z‖
  let B₀ := K * ((coupling⁻¹) ^ 2 * Real.exp (-coupling * (G + J)) * F₀ +
    Real.exp (-coupling * J) * Fc)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀, F₀, Fc]; positivity
  have hbase : B₀ ≤ A * (c * Γ) * coupling ^ 6 * Real.exp (-coupling * (G + J)) :=
    oppositeSupport_source_envelope_le hc1 hΓ hcc hK.le
      (coreSourceConstant_pos p).le hCs.le hCΓ.le hinv
      (show 0 ≤ p.β / 2 by linarith [hp.β_pos]) hF₀ hFc
  have hscaled : B₀ ^ 2 * Vnorm ≤
      (A ^ 2 * (Vnorm + 1)) * c ^ 2 * Γ ^ 2 * coupling ^ 12 *
        Real.exp (-2 * coupling * (G + J)) := by
    have hexp : Real.exp (-coupling * (G + J)) ^ 2 =
        Real.exp (-2 * coupling * (G + J)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (A * (c * Γ) * coupling ^ 6 * Real.exp (-coupling * (G + J))) ^ 2 * Vnorm :=
        mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ hB₀ (by positivity)).mpr hbase) hVnorm
      _ = A ^ 2 * Vnorm * c ^ 2 * Γ ^ 2 * coupling ^ 12 *
          Real.exp (-2 * coupling * (G + J)) := by
        simp only [mul_pow, ← pow_mul, hexp]
        ring
      _ ≤ _ := by gcongr; linarith
  exact ⟨hΓ, hraw.1.trans hscaled, hraw.2.trans hscaled⟩

end CuspParameters
end InfiniteZero
