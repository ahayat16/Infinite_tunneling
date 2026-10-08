import InfiniteZero.AtomicActiveScatteredRelative
import InfiniteZero.CanonicalInactiveRelative

/-!
# Simultaneous physical witnesses for the canonical channels

The active estimate chooses one positive radial reference, one full ground
state and their actual coefficients. The universal inactive estimate then
uses those same witnesses. No regularity of the choices in the coupling
is asserted or needed. All constants and the common threshold precede
the coupling.
-/

noncomputable section
open Set

namespace InfiniteZero

structure ConcreteChannelWitnesses (p : CuspParameters) (L : ℝ) where
  φ : ℝ → Wavefunction
  ψ : ℝ → Wavefunction
  c : ℝ → ℝ
  Γ : ℝ → ℝ
  Cactive : ℝ
  Cinactive : ℝ
  threshold : ℝ
  Cactive_pos : 0 < Cactive
  Cinactive_pos : 0 < Cinactive
  threshold_pos : 0 < threshold
  core_ground : ∀ coupling, threshold ≤ coupling →
    IsAtomicGroundState p.b p.core coupling (φ coupling)
  core_positive : ∀ coupling, threshold ≤ coupling → IsPositiveRadial (φ coupling)
  full_ground : ∀ coupling, threshold ≤ coupling →
    IsAtomicGroundState p.b p.potential coupling (ψ coupling)
  c_range : ∀ coupling, threshold ≤ coupling → c coupling ∈ Icc (1 / 2 : ℝ) 1
  Γ_pos : ∀ coupling, threshold ≤ coupling → 0 < Γ coupling
  tail : ∀ coupling, threshold ≤ coupling → ∀ x : Plane, p.r₀ < ‖x‖ →
    φ coupling x = (Γ coupling * landauKernel p.b coupling⁻¹
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)
  energy_range : ∀ coupling, threshold ≤ coupling →
    scaledAtomicEnergy p coupling ∈ Icc (1 / 2 : ℝ) 1
  envelope_pos : ∀ coupling, threshold ≤ coupling →
    0 < p.activeSaddleTexEnvelope L coupling (c coupling) (Γ coupling)
  active_bound : ∀ coupling, threshold ≤ coupling →
    ‖canonicalSourceCell p L coupling 1 2 -
      sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling)
        (fun x => (c coupling : ℂ) * φ coupling x) 1 2‖ ≤
      Cactive * p.activeSaddleTexEnvelope L coupling (c coupling) (Γ coupling) *
        Real.exp (-(p.β / 8) * (Real.log coupling) ^ 2)
  inactive_bound : ∀ coupling, threshold ≤ coupling → ∀ i j : Fin 3,
    (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
      ‖canonicalSourceCell p L coupling i j‖ ≤
        Cinactive * p.activeSaddleTexEnvelope L coupling (c coupling) (Γ coupling) *
          Real.exp (-15 * p.hopMargin * coupling)
  inactive_sum_bound : ∀ coupling, threshold ≤ coupling →
    inactiveCellNormSum (canonicalSourceCell p L coupling) ≤
      Cinactive * p.activeSaddleTexEnvelope L coupling (c coupling) (Γ coupling) *
        Real.exp (-15 * p.hopMargin * coupling)

namespace CuspParameters

theorem exists_concreteChannelWitnesses_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) : Nonempty (ConcreteChannelWitnesses p L) := by
  have hRL : p.R < 2 * L := by
    have hR : p.R < L :=
      ((le_max_right cert.supportRadius p.R).trans_lt cert.separation).trans_le hL
    linarith [hp.radius_pos]
  obtain ⟨Ca, hCa, Ta, hTa, hactive⟩ :=
    exists_atomicGround_active_scattered_relative_of_radialData
      hInterior hp hRad hAcore hApot χ hRL
      (β₀ := 3 * p.β / 4) (by linarith [hp.β_pos])
      (by linarith [hp.β_pos]) (by linarith [hp.β_pos])
  obtain ⟨Ci, hCi, Ti, _hTi, hinactive⟩ :=
    exists_canonical_inactive_relative_tex_of_radialData
      hInterior hp hRad hAcore hApot χ cert hL
  let T := max Ta Ti
  have hT : 0 < T := hTa.trans_le (le_max_left _ _)
  have hstates : ∀ coupling : ℝ, ∃ φ ψ : Wavefunction, ∃ c Γ : ℝ,
      IsAtomicGroundState p.b p.core (max T coupling) φ ∧ IsPositiveRadial φ ∧
      IsAtomicGroundState p.b p.potential (max T coupling) ψ ∧
      c ∈ Icc (1 / 2 : ℝ) 1 ∧ 0 < Γ ∧
      (∀ x : Plane, p.r₀ < ‖x‖ →
        φ x = (Γ * landauKernel p.b (max T coupling)⁻¹
          (-(((max T coupling)⁻¹) ^ 2 *
            atomicGroundEnergy p.b p.core (max T coupling))) ‖x‖ : ℂ)) ∧
      scaledAtomicEnergy p (max T coupling) ∈ Icc (1 / 2 : ℝ) 1 ∧
      0 < p.activeSaddleTexEnvelope L (max T coupling) c Γ ∧
      ‖canonicalSourceCell p L (max T coupling) 1 2 -
        sourceCell p L (max T coupling)⁻¹ (scaledAtomicEnergy p (max T coupling))
          (fun x => (c : ℂ) * φ x) 1 2‖ ≤
        Ca * p.activeSaddleTexEnvelope L (max T coupling) c Γ *
          Real.exp (-(p.β / 8) * (Real.log (max T coupling)) ^ 2) ∧
      (∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
        ‖canonicalSourceCell p L (max T coupling) i j‖ ≤
          Ci * p.activeSaddleTexEnvelope L (max T coupling) c Γ *
            Real.exp (-15 * p.hopMargin * (max T coupling))) ∧
      inactiveCellNormSum (canonicalSourceCell p L (max T coupling)) ≤
        Ci * p.activeSaddleTexEnvelope L (max T coupling) c Γ *
          Real.exp (-15 * p.hopMargin * (max T coupling)) := by
    intro coupling
    have ha : Ta ≤ max T coupling := (le_max_left Ta Ti).trans (le_max_left _ _)
    have hi : Ti ≤ max T coupling := (le_max_right Ta Ti).trans (le_max_left _ _)
    obtain ⟨φ, ψ, hφ, hpos, hψ, c, hc, Γ, hΓ, htail, hE,
      _hηsmooth, _hηLp, _horth, henv, _hactual, hcanonical⟩ := hactive (max T coupling) ha
    obtain ⟨_henv, hicells, hisum⟩ :=
      hinactive (max T coupling) hi φ hφ hpos Γ hΓ htail c hc.1
    refine ⟨φ, ψ, c, Γ, hφ, hpos, hψ, hc, hΓ, htail, hE, henv, ?_, hicells, hisum⟩
    simpa only [show (3 * (3 * p.β / 4) - 2 * p.β) / 2 = p.β / 8 by ring]
      using hcanonical
  choose φ ψ c Γ hcore hpos hfull hc hΓ htail hE henv hactive hinactive hsum using hstates
  refine ⟨{
    φ := φ
    ψ := ψ
    c := c
    Γ := Γ
    Cactive := Ca
    Cinactive := Ci
    threshold := T
    Cactive_pos := hCa
    Cinactive_pos := hCi
    threshold_pos := hT
    core_ground := ?_
    core_positive := ?_
    full_ground := ?_
    c_range := ?_
    Γ_pos := ?_
    tail := ?_
    energy_range := ?_
    envelope_pos := ?_
    active_bound := ?_
    inactive_bound := ?_
    inactive_sum_bound := ?_ }⟩
  all_goals intro coupling hcoupling
  · simpa only [max_eq_right hcoupling] using hcore coupling
  · exact hpos coupling
  · simpa only [max_eq_right hcoupling] using hfull coupling
  · exact hc coupling
  · exact hΓ coupling
  · simpa only [max_eq_right hcoupling] using htail coupling
  · simpa only [max_eq_right hcoupling] using hE coupling
  · simpa only [max_eq_right hcoupling] using henv coupling
  · simpa only [max_eq_right hcoupling] using hactive coupling
  · simpa only [max_eq_right hcoupling] using hinactive coupling
  · simpa only [max_eq_right hcoupling] using hsum coupling

end CuspParameters
end InfiniteZero
