import InfiniteZero.DoubleWellLocalizedEstimates
import InfiniteZero.MagneticIMSThree
import InfiniteZero.TranslatedAtomicGap
import InfiniteZero.AtomicGroundAgmon
import InfiniteZero.DoubleWellCoercivityScalar

/-!
# Two-well coercivity on actual test functions

The fixed three-piece localization combines the quantitative gap of each
translated full atom and the nonnegative exterior kinetic energy. Only the
original two overlaps remain, with a loss controlled by the actual atomic
tail beyond `4 r₀`. All constants are fixed before the well separation.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero.CuspParameters

/-- The full physical localization bound before absorption of its losses. -/
theorem doubleWell_test_rankTwo_lower
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) {coupling E g C : ℝ}
    (hg : 0 ≤ g) (hE : g ≤ -E) (hC : 0 ≤ C)
    (herrorL : ∀ x, magneticIMSError (doubleWellLeftCutoff hp cert L)
      (doubleWellLeftOuterCutoff hp cert L) x ≤ C)
    (herrorR : ∀ x, magneticIMSError (doubleWellRightCutoff hp cert L)
      (doubleWellRightOuterCutoff hp cert L) x ≤ C)
    {φ ψ : Wavefunction} (hφ : MemLp φ 2 volume) (hψ : IsTestFunction ψ)
    (hgapL : ∀ u : Wavefunction, IsTestFunction u →
      g * (mass u - ‖waveInner (leftState p.b L coupling φ) u‖ ^ 2) ≤
        magneticForm p.b coupling (fun x => p.potential (x + displacement L)) u - E * mass u)
    (hgapR : ∀ u : Wavefunction, IsTestFunction u →
      g * (mass u - ‖waveInner (rightState p.b L coupling φ) u‖ ^ 2) ≤
        magneticForm p.b coupling (fun x => p.potential (displacement L - x)) u - E * mass u) :
    (g - 4 * g * (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - 2 * C) * mass ψ -
      2 * g * (‖waveInner (leftState p.b L coupling φ) ψ‖ ^ 2 +
        ‖waveInner (rightState p.b L coupling φ) ψ‖ ^ 2) ≤
      magneticForm p.b coupling (doubleWellPotential p.potential L) ψ - E * mass ψ := by
  let uL : Wavefunction := fun x => (doubleWellLeftCutoff hp cert L x : ℂ) * ψ x
  let uR : Wavefunction := fun x => (doubleWellRightCutoff hp cert L x : ℂ) * ψ x
  let uX : Wavefunction := fun x => (doubleWellExteriorCutoff hp cert L x : ℂ) * ψ x
  let tail := ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2
  have hleft := hgapL uL (hψ.real_mul (doubleWellLeftCutoff_contDiff hp cert L))
  have hright := hgapR uR (hψ.real_mul (doubleWellRightCutoff_contDiff hp cert L))
  rw [← doubleWellLeftCutoff_form_eq hp cert hL coupling ψ] at hleft
  rw [← doubleWellRightCutoff_form_eq hp cert hL coupling ψ] at hright
  have hext : g * mass uX ≤
      magneticForm p.b coupling (doubleWellPotential p.potential L) uX - E * mass uX := by
    have hk := doubleWellExteriorCutoff_form_nonneg hp cert L coupling ψ
    have hm := mul_le_mul_of_nonneg_right hE (mass_nonneg uX)
    linarith only [hk, hm]
  have hovL := norm_waveInner_doubleWellLeftCutoff_sq_le hp cert L coupling hφ hψ.memLp
  have hovR := norm_waveInner_doubleWellRightCutoff_sq_le hp cert L coupling hφ hψ.memLp
  have hmulL := mul_le_mul_of_nonneg_left hovL hg
  have hmulR := mul_le_mul_of_nonneg_left hovR hg
  have hm := mass_ims_three hψ
    (doubleWellLeftCutoff_contDiff hp cert L) (doubleWellLeftOuterCutoff_contDiff hp cert L)
    (doubleWellRightCutoff_contDiff hp cert L) (doubleWellRightOuterCutoff_contDiff hp cert L)
    (doubleWellLeftCutoffs_partition hp cert L) (doubleWellRightCutoffs_partition hp cert L)
    (doubleWellLeftOuterCutoff_mul_rightCutoff hp cert hL)
  simp only [doubleWellRightOuterCutoff_mul_leftOuterCutoff] at hm
  change mass uL + mass uR + mass uX = mass ψ at hm
  have hmg := congrArg (fun z : ℝ => g * z) hm
  have hV : Continuous (doubleWellPotential p.potential L) := by
    exact ((potential_contDiff hp).continuous.comp (continuous_id.add continuous_const)).add
      ((potential_contDiff hp).continuous.comp (continuous_id.neg.add continuous_const))
  have hi := magneticForm_sub_mass_ims_three_lower p.b coupling E hV hψ
    (doubleWellLeftCutoff_contDiff hp cert L) (doubleWellLeftOuterCutoff_contDiff hp cert L)
    (doubleWellRightCutoff_contDiff hp cert L) (doubleWellRightOuterCutoff_contDiff hp cert L)
    (doubleWellLeftCutoffs_partition hp cert L) (doubleWellRightCutoffs_partition hp cert L)
    (doubleWellLeftOuterCutoff_mul_rightCutoff hp cert hL) hC hC herrorL herrorR
    (fun x => by rw [abs_of_nonneg (doubleWellLeftOuterCutoff_range hp cert L x).1]
                 exact (doubleWellLeftOuterCutoff_range hp cert L x).2)
  simp only [doubleWellRightOuterCutoff_mul_leftOuterCutoff] at hi
  change (magneticForm p.b coupling (doubleWellPotential p.potential L) uL - E * mass uL) +
    (magneticForm p.b coupling (doubleWellPotential p.potential L) uR - E * mass uR) +
    (magneticForm p.b coupling (doubleWellPotential p.potential L) uX - E * mass uX) -
    (C + C) * mass ψ ≤ _ at hi
  change (g - 4 * g * tail - 2 * C) * mass ψ - _ ≤ _
  change g * ‖waveInner (leftState p.b L coupling φ) uL‖ ^ 2 ≤
    g * (2 * ‖waveInner (leftState p.b L coupling φ) ψ‖ ^ 2 + 2 * tail * mass ψ) at hmulL
  change g * ‖waveInner (rightState p.b L coupling φ) uR‖ ^ 2 ≤
    g * (2 * ‖waveInner (rightState p.b L coupling φ) ψ‖ ^ 2 + 2 * tail * mass ψ) at hmulR
  nlinarith only [hleft, hright, hext, hi, hmg, hmulL, hmulR]

/-- The physical two-well estimate, uniform in separation, after absorbing
the actual atomic tail and the fixed IMS losses. -/
theorem exists_doubleWell_test_rankTwo_gap_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ ψ : Wavefunction, IsTestFunction ψ →
        (hRad.gap / 4 * coupling) * mass ψ -
          (hRad.gap * coupling) *
            (‖waveInner (leftState p.b L coupling φ) ψ‖ ^ 2 +
              ‖waveInner (rightState p.b L coupling φ) ψ‖ ^ 2) ≤
        magneticForm p.b coupling (doubleWellPotential p.potential L) ψ -
          atomicGroundEnergy p.b p.potential coupling * mass ψ := by
  obtain ⟨D, hD, hims⟩ := exists_doubleWellIMSError_bound hp cert
  obtain ⟨C, hC, d, hd, Ta, _, htail⟩ :=
    exists_atomicGround_agmon_tail_of_radialData hp hRad hAcore hApot
  obtain ⟨Tg, _, hgap⟩ :=
    exists_translated_atomic_test_rankOne_gap_of_radialData hp hRad hAcore hApot
  obtain ⟨Te, _, henergy⟩ :=
    exists_atomicGroundEnergy_bounds_of_radialData hp hRad hAcore hApot
  obtain ⟨Ts, hTs, habsorb⟩ := exists_twoWell_coercivity_absorption_threshold
    (show 0 < hRad.gap / 2 from div_pos hRad.gap_pos (by norm_num)) C D hRad.energyBound
  let T := max Ts (max Ta (max Tg Te))
  refine ⟨T, hTs.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcTs : Ts ≤ coupling := (le_max_left _ _).trans hc
  have hrest : max Ta (max Tg Te) ≤ coupling := (le_max_right _ _).trans hc
  have hcTa : Ta ≤ coupling := (le_max_left _ _).trans hrest
  have hrest' : max Tg Te ≤ coupling := (le_max_right _ _).trans hrest
  have hcTg : Tg ≤ coupling := (le_max_left _ _).trans hrest'
  have hcTe : Te ≤ coupling := (le_max_right _ _).trans hrest'
  obtain ⟨hcpos, hreserve, habs⟩ := habsorb coupling hcTs
  refine ⟨(htail coupling hcTa).1, ?_⟩
  intro L hL φ hφ ψ hψ
  let g := hRad.gap / 2 * coupling
  have hg : 0 ≤ g := mul_nonneg (div_pos hRad.gap_pos (by norm_num)).le hcpos.le
  have hE : g ≤ -atomicGroundEnergy p.b p.potential coupling := by
    have he := (henergy coupling hcTe).2
    dsimp [g]
    linarith only [hreserve, he]
  have htail' : (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤ C / coupling ^ 2 := by
    apply ((htail coupling hcTa).2.1 φ hφ).trans
    have hexp : Real.exp (-2 * d * coupling) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_pos hd hcpos]
    exact (mul_le_mul_of_nonneg_left hexp (div_nonneg hC.le (sq_nonneg coupling))).trans_eq
      (mul_one _)
  have hcoefficient : hRad.gap / 4 * coupling ≤
      g - 4 * g * (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) - 2 * D := by
    have hm := mul_le_mul_of_nonneg_left htail' (show 0 ≤ 4 * g by positivity)
    change hRad.gap / 2 / 2 * coupling ≤ g - 4 * g * (C / coupling ^ 2) - 2 * D at habs
    nlinarith only [habs, hm]
  have hlocal := doubleWell_test_rankTwo_lower hp cert hL hg hE hD.le
    (fun x => (hims L x).1) (fun x => (hims L x).2) hφ.1.2.1 hψ
    (fun u hu => (hgap coupling hcTg L φ hφ u hu).1)
    (fun u hu => (hgap coupling hcTg L φ hφ u hu).2)
  have h := (sub_le_sub_right
    (mul_le_mul_of_nonneg_right hcoefficient (mass_nonneg ψ))
    (2 * g * (‖waveInner (leftState p.b L coupling φ) ψ‖ ^ 2 +
      ‖waveInner (rightState p.b L coupling φ) ψ‖ ^ 2))).trans hlocal
  convert h using 1
  dsimp [g]
  ring

end InfiniteZero.CuspParameters
