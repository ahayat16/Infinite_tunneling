import InfiniteZero.DoubleWellTestCoercivity
import InfiniteZero.MagneticGraphTwoModeLowerBound

/-!
# Physical two-well coercivity on the actual closed operator domain

The test inequality passes to the specified closed graph by continuity.
The references can be any L² representatives of the two translated atomic
states. Orthogonality to both removes the two overlap losses and leaves
an order-coupling gap above the single-well energy on their complement.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem exists_doubleWell_operator_rankTwo_gap_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ vL vR : L2Space, Represents vL (leftState p.b L coupling φ) →
        Represents vR (rightState p.b L coupling φ) →
      ∀ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
        (hRad.gap / 4 * coupling) * ‖(u : L2Space)‖ ^ 2 -
          (hRad.gap * coupling) *
            (‖inner ℂ vL (u : L2Space)‖ ^ 2 + ‖inner ℂ vR (u : L2Space)‖ ^ 2) ≤
        (inner ℂ (u : L2Space)
          (magneticOperator p.b coupling (doubleWellPotential p.potential L) u)).re -
          atomicGroundEnergy p.b p.potential coupling * ‖(u : L2Space)‖ ^ 2 := by
  obtain ⟨T, hT, htest⟩ := exists_doubleWell_test_rankTwo_gap_of_radialData
    hp cert hRad hAcore hApot
  refine ⟨T, hT, ?_⟩
  intro coupling hc
  refine ⟨(htest coupling hc).1, ?_⟩
  intro L hL φ hφ vL vR hvL hvR u
  have hV : Continuous (doubleWellPotential p.potential L) :=
    ((potential_contDiff hp).continuous.comp (continuous_id.add continuous_const)).add
      ((potential_contDiff hp).continuous.comp (continuous_id.neg.add continuous_const))
  have h := (hAdouble coupling L).rankTwo_lower hV hvL.memLp hvR.memLp
    ((htest coupling hc).2 L hL φ hφ) u
  rw [hvL.toLp_eq hvL.memLp, hvR.toLp_eq hvR.memLp] at h
  exact h

theorem exists_doubleWell_operator_complement_gap_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (∃ φ, IsAtomicGroundState p.b p.potential coupling φ) ∧
      ∀ L : ℝ, cert.L₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ vL vR : L2Space, Represents vL (leftState p.b L coupling φ) →
        Represents vR (rightState p.b L coupling φ) →
      ∀ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
        inner ℂ vL (u : L2Space) = 0 → inner ℂ vR (u : L2Space) = 0 →
        (atomicGroundEnergy p.b p.potential coupling + hRad.gap / 4 * coupling) *
          ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator p.b coupling (doubleWellPotential p.potential L) u)).re := by
  obtain ⟨T, hT, hbound⟩ := exists_doubleWell_operator_rankTwo_gap_of_radialData
    hp cert hRad hAcore hApot hAdouble
  refine ⟨T, hT, ?_⟩
  intro coupling hc
  refine ⟨(hbound coupling hc).1, ?_⟩
  intro L hL φ hφ vL vR hvL hvR u huL huR
  have h := (hbound coupling hc).2 L hL φ hφ vL vR hvL hvR u
  simp only [huL, huR, norm_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero, mul_zero, sub_zero] at h
  nlinarith only [h]

end InfiniteZero.CuspParameters
