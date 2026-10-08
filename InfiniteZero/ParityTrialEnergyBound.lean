import InfiniteZero.DoubleWellTrialResidualBound
import InfiniteZero.AtomicTranslatedOverlap
import InfiniteZero.SchurResidualBounds

/-!
# A coarse upper energy bound for the actual parity trials

The opposite-well residual is exponentially small. Normalization costs at
most one when the overlap is at most one half, so the sum and difference
have residual at most twice the one-well residual. This gives an upper
Rayleigh bound with an explicit positive error above the atomic energy.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InfiniteZero

theorem norm_parityTrial_normalization_le_one
    {b L coupling : ℝ} {φ : Wavefunction} (even : Bool)
    (hs : |translatedOverlap b L coupling φ| ≤ 1 / 2) :
    ‖((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ)‖ ≤ 1 := by
  have hm : 1 ≤ parityTrialMass even b L coupling φ := by
    obtain ⟨hl, hr⟩ := abs_le.mp hs
    cases even <;> simp only [parityTrialMass, Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hsqrt : 1 ≤ Real.sqrt (parityTrialMass even b L coupling φ) :=
    Real.one_le_sqrt.mpr hm
  simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using inv_le_one_of_one_le₀ hsqrt

private theorem norm_normalized_parity_residual_le
    (A : L2Space →ₗ.[ℂ] L2Space) (E R : ℝ) (uLeft uRight : A.domain)
    (hLeft : ‖A uLeft - (E : ℂ) • (uLeft : L2Space)‖ ≤ R)
    (hRight : ‖A uRight - (E : ℂ) • (uRight : L2Space)‖ ≤ R)
    (even : Bool) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖A (c • (if even then uLeft + uRight else uLeft - uRight)) -
      (E : ℂ) • ((c • (if even then uLeft + uRight else uLeft - uRight) : A.domain) : L2Space)‖
      ≤ 2 * R := by
  let uRaw : A.domain := if even then uLeft + uRight else uLeft - uRight
  have hraw : ‖A uRaw - (E : ℂ) • (uRaw : L2Space)‖ ≤ 2 * R := by
    cases even
    · change ‖A (uLeft - uRight) - (E : ℂ) • ((uLeft - uRight : A.domain) : L2Space)‖ ≤ _
      simp only [LinearPMap.map_sub, Submodule.coe_sub, smul_sub]
      rw [show A uLeft - A uRight - ((E : ℂ) • (uLeft : L2Space) -
          (E : ℂ) • (uRight : L2Space)) =
          (A uLeft - (E : ℂ) • (uLeft : L2Space)) -
          (A uRight - (E : ℂ) • (uRight : L2Space)) by abel]
      exact (norm_sub_le _ _).trans (by linarith)
    · change ‖A (uLeft + uRight) - (E : ℂ) • ((uLeft + uRight : A.domain) : L2Space)‖ ≤ _
      simp only [LinearPMap.map_add, Submodule.coe_add, smul_add]
      rw [show A uLeft + A uRight - ((E : ℂ) • (uLeft : L2Space) +
          (E : ℂ) • (uRight : L2Space)) =
          (A uLeft - (E : ℂ) • (uLeft : L2Space)) +
          (A uRight - (E : ℂ) • (uRight : L2Space)) by abel]
      exact (norm_add_le _ _).trans (by linarith)
  change ‖A (c • uRaw) - (E : ℂ) • ((c • uRaw : A.domain) : L2Space)‖ ≤ _
  rw [LinearPMap.map_smul, Submodule.coe_smul, smul_comm (E : ℂ) c,
    ← smul_sub, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans hraw

namespace CuspParameters

theorem exists_parityTrial_operator_vector_residual_le {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {coupling L C d : ℝ} (hc : 0 < coupling) (hL : cert.L₀ ≤ L) (hC : 0 ≤ C)
    {φ : Wavefunction} (hφ : IsAtomicGroundState p.b p.potential coupling φ)
    (hs : |translatedOverlap p.b L coupling φ| ≤ 1 / 2)
    (htail : (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
      (C / coupling ^ 2) * Real.exp (-2 * d * coupling))
    (hAleft : IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : IsMagneticRealization p.b coupling (doubleWellPotential p.potential L))
    (even : Bool) :
    ∃ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
      Represents (u : L2Space) (normalizedParityTrialState even p.b L coupling φ) ∧
      ‖(u : L2Space)‖ = 1 ∧ HasL2Parity even (u : L2Space) ∧
      ‖magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
          (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space)‖ ≤
        2 * (Real.sqrt C * coupling * Real.exp (-d * coupling)) := by
  obtain ⟨uLeft, hLeft, _, hresLeft⟩ := exists_leftState_double_operator_vector_residual_le
    hp cert hc hL hC hφ htail hAleft hAdouble
  obtain ⟨uRight, hRight, _, hresRight⟩ := exists_rightState_double_operator_vector_residual_le
    hp cert hc hL hC hφ htail hAright hAdouble
  let A := magneticOperator p.b coupling (doubleWellPotential p.potential L)
  let uRaw : A.domain := if even then uLeft + uRight else uLeft - uRight
  have hRaw : Represents (uRaw : L2Space) (parityTrialState even p.b L coupling φ) := by
    cases even
    · change Represents ((uLeft : L2Space) - (uRight : L2Space))
        (leftState p.b L coupling φ - rightState p.b L coupling φ)
      filter_upwards [Lp.coeFn_sub (uLeft : L2Space) (uRight : L2Space),
        hLeft, hRight] with x hx hxl hxr
      simpa only [Pi.sub_apply, hxl, hxr] using hx
    · change Represents ((uLeft : L2Space) + (uRight : L2Space))
        (leftState p.b L coupling φ + rightState p.b L coupling φ)
      filter_upwards [Lp.coeFn_add (uLeft : L2Space) (uRight : L2Space),
        hLeft, hRight] with x hx hxl hxr
      simpa only [Pi.add_apply, hxl, hxr] using hx
  let c : ℂ := ((Real.sqrt (parityTrialMass even p.b L coupling φ))⁻¹ : ℂ)
  let u : A.domain := c • uRaw
  have hu : Represents (u : L2Space) (normalizedParityTrialState even p.b L coupling φ) := by
    change Represents (c • (uRaw : L2Space)) (c • parityTrialState even p.b L coupling φ)
    filter_upwards [Lp.coeFn_smul c (uRaw : L2Space), hRaw] with x hx hraw
    simpa only [Pi.smul_apply, hraw] using hx
  have hn : ‖(u : L2Space)‖ = 1 := by
    have hnorm := hu.norm_sq_eq_mass.trans
      (mass_normalizedParityTrialState even p.b L coupling hφ.1.2.1 hφ.2
        (hs.trans_lt (by norm_num)))
    nlinarith [norm_nonneg (u : L2Space)]
  exact ⟨u, hu, hn, hu.hasL2Parity (normalizedParityTrialState_hasParity even p.b L coupling φ),
    norm_normalized_parity_residual_le A _ _ uLeft uRight hresLeft hresRight even c
      (norm_parityTrial_normalization_le_one even hs)⟩

/-- The threshold is independent of the well separation, ground-state phase,
parity, and the local realization witnesses. The trial energy may lie above
the atomic energy, by at most the displayed positive error. -/
theorem exists_parityTrial_energy_upper_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ (_hAleft : IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
        (_hAright : IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
        (_hAdouble : IsMagneticRealization p.b coupling (doubleWellPotential p.potential L))
        (even : Bool),
      ∃ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
        Represents (u : L2Space) (normalizedParityTrialState even p.b L coupling φ) ∧
        ‖(u : L2Space)‖ = 1 ∧ HasL2Parity even (u : L2Space) ∧
        ‖magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
          (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space)‖ ≤
            (hRad.gap / 8) * coupling ∧
        schurDiagonal (magneticOperator p.b coupling (doubleWellPotential p.potential L)) u ≤
          atomicGroundEnergy p.b p.potential coupling + (hRad.gap / 8) * coupling := by
  obtain ⟨C, hC, d, hd, Ta, hTa, htail⟩ :=
    exists_atomicGround_agmon_tail_of_radialData hp hRad hAcore hApot
  obtain ⟨Ts, _, hsmall⟩ := exists_translatedOverlap_uniform_small_of_radialData
    hp hRad hAcore hApot (by norm_num : (0 : ℝ) < 1 / 2)
  have he : Tendsto (fun coupling : ℝ => 2 * Real.sqrt C * Real.exp (-d * coupling))
      atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop_of_neg
        (neg_neg_of_pos hd))
    simpa only [Function.comp_def, mul_zero] using he.const_mul (2 * Real.sqrt C)
  obtain ⟨Te, hTe⟩ := eventually_atTop.mp
    (he.eventually (Iio_mem_nhds (div_pos hRad.gap_pos (by norm_num) : 0 < hRad.gap / 8)))
  refine ⟨max Ta (max Ts Te), hTa.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL φ hφ hAleft hAright hAdouble even
  have hca : Ta ≤ coupling := (le_max_left _ _).trans hc
  have hcs : Ts ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hce : Te ≤ coupling := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hcpos : 0 < coupling := hTa.trans_le hca
  have hfour : 4 * p.r₀ ≤ L := by
    have hR : p.R < L := ((le_max_right _ _).trans_lt cert.separation).trans_le hL
    linarith [hp.radius_large, hp.r₀_pos]
  obtain ⟨u, hu, hn, hp, hr⟩ := exists_parityTrial_operator_vector_residual_le
    hp cert hcpos hL hC.le hφ (hsmall coupling hcs L hfour φ hφ).le
      ((htail coupling hca).2.1 φ hφ) hAleft hAright hAdouble even
  have hres : ‖magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
      (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space)‖ ≤
      (hRad.gap / 8) * coupling := hr.trans (by
    have hm := mul_le_mul_of_nonneg_right (hTe coupling hce).le hcpos.le
    nlinarith only [hm])
  refine ⟨u, hu, hn, hp, hres, ?_⟩
  have hdiag := schurDiagonal_sub_reference_le_residual
    (magneticOperator p.b coupling (doubleWellPotential p.potential L)) u hn
    (atomicGroundEnergy p.b p.potential coupling)
    (magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
      (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space))
    (by abel)
  have hh := (le_abs_self _).trans (hdiag.trans hres)
  linarith only [hh]

end CuspParameters
end InfiniteZero
