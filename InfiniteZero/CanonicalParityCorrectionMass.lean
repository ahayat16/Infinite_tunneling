import InfiniteZero.CanonicalParityCorrection
import InfiniteZero.PhysicalResidualMass

/-!
# Physical opposite-well mass controls the canonical Schur corrections

No residual is an assumed small quantity: the actual operator equations
identify it with the opposite potential times the translated atomic state.
The quadratic Schur estimate then costs only three powers of the coupling.
-/

noncomputable section
namespace InfiniteZero

def canonicalOppositeMass (b : ℝ) (v : Potential) (L coupling : ℝ) : ℝ :=
  mass (fun x => (v (x + displacement L) : ℂ) *
    rightState b L coupling (canonicalAtomicState b v coupling) x)

theorem canonicalDefect_eq_right (b : ℝ) (v : Potential) (L coupling : ℝ) :
    canonicalDefect b v L coupling = coupling ^ 2 *
      ∫ x : Plane, v (x + displacement L) *
        ‖rightState b L coupling (canonicalAtomicState b v coupling) x‖ ^ 2 :=
  translatedDefect_eq_right b v L coupling (canonicalAtomicState b v coupling)

namespace CuspParameters

theorem exists_canonicalParityCorrection_mass_bounds_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, cert.L₀ ≤ L →
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)) →
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)) →
      ∀ even : Bool, 0 ≤ canonicalParityCorrection p.b p.potential L coupling even ∧
        canonicalParityCorrection p.b p.potential L coupling even ≤
          (32 / hRad.gap) * coupling ^ 3 * canonicalOppositeMass p.b p.potential L coupling := by
  obtain ⟨Tg, hTg, hshift⟩ := exists_canonicalParityCorrection_residual_bounds_of_radialData
    hp cert hRad hAcore hApot hAdouble
  obtain ⟨Ta, _, hatom⟩ := eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  obtain ⟨Ts, _, hsmall⟩ := exists_canonicalOverlap_uniform_small_of_radialData
    hp hRad hAcore hApot (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨max Tg (max Ta Ts), hTg.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL hAleft hAright even
  have hcg : Tg ≤ coupling := (le_max_left _ _).trans hc
  have hca : Ta ≤ coupling := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcs : Ts ≤ coupling := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hcpos : 0 < coupling := hTg.trans_le hcg
  have hφ := canonicalAtomicState_spec p.b p.potential coupling (hatom coupling hca).1
  have hfour : 4 * p.r₀ ≤ L := by
    have hR : p.R < L := ((le_max_right _ _).trans_lt cert.separation).trans_le hL
    linarith [hp.radius_large, hp.r₀_pos]
  have hs := hsmall coupling hcs L hfour
  have hbound : ∀ x, |p.potential x| ≤ 1 := by
    intro x
    obtain ⟨hl, hr⟩ := potential_range hp x
    exact abs_le.mpr ⟨hl, hr.trans (by norm_num)⟩
  obtain ⟨u, hu, _, _⟩ := hφ.exists_normalizedParityTrialState_unit_operator_vector
    (potential_contDiff hp).continuous hbound hAleft hAright (hAdouble coupling L)
    even (hs.trans (by norm_num))
  obtain ⟨h0, hσ⟩ := hshift coupling hcg L hL hAleft hAright even u hu
  have hres := hφ.normalizedParityTrial_residual_sq_le_mass
    (potential_contDiff hp).continuous hbound hAleft hAright (hAdouble coupling L)
    even hs.le u hu
  have hg : 0 < hRad.gap / 8 * coupling :=
    mul_pos (div_pos hRad.gap_pos (by norm_num)) hcpos
  refine ⟨h0, hσ.trans ?_⟩
  calc
    _ ≤ (4 * coupling ^ 4 * canonicalOppositeMass p.b p.potential L coupling) /
        (hRad.gap / 8 * coupling) := div_le_div_of_nonneg_right hres hg.le
    _ = (32 / hRad.gap) * coupling ^ 3 *
        canonicalOppositeMass p.b p.potential L coupling := by
      field_simp
      ring

end CuspParameters
end InfiniteZero
