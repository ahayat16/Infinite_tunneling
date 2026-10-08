import InfiniteZero.MagneticTrialCovariance
import InfiniteZero.AtomicGroundRankOne

/-!
# The atomic rank-one gap at both translated wells

Testing with the inverse magnetic translation transports the exact test
inequality to a translated potential. Inversion transports it to the other
well. Applied to the actual full atomic ground state, these operations leave
the gap and the large-coupling threshold unchanged for every separation.
-/

noncomputable section

namespace InfiniteZero

theorem test_rankOne_bound_magneticTranslation
    {b coupling g E : ℝ} {V : Potential} {φ : Wavefunction}
    (hgap : ∀ ψ : Wavefunction, IsTestFunction ψ →
      g * (mass ψ - ‖waveInner φ ψ‖ ^ 2) ≤
        magneticForm b coupling V ψ - E * mass ψ)
    (a : Plane) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    g * (mass ψ - ‖waveInner (magneticTranslation b coupling a φ) ψ‖ ^ 2) ≤
      magneticForm b coupling (fun x => V (x - a)) ψ - E * mass ψ := by
  have htest := hψ.magneticTranslated b coupling (-a)
  have h := hgap (magneticTranslation b coupling (-a) ψ) htest
  have hinner := waveInner_magneticTranslation b coupling a φ
    (magneticTranslation b coupling (-a) ψ)
  have hform := magneticForm_magneticTranslation b coupling a V htest
  rw [magneticTranslation_cancel_neg] at hinner hform
  rw [mass_magneticTranslation, ← hinner, ← hform] at h
  exact h

theorem test_rankOne_bound_inversion
    {b coupling g E : ℝ} {V : Potential} {φ : Wavefunction}
    (hgap : ∀ ψ : Wavefunction, IsTestFunction ψ →
      g * (mass ψ - ‖waveInner φ ψ‖ ^ 2) ≤
        magneticForm b coupling V ψ - E * mass ψ)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    g * (mass ψ - ‖waveInner (fun x => φ (-x)) ψ‖ ^ 2) ≤
      magneticForm b coupling (fun x => V (-x)) ψ - E * mass ψ := by
  have h := hgap (fun x => ψ (-x)) hψ.inversion
  have hinner := waveInner_inversion φ (fun x => ψ (-x))
  have hform := magneticForm_inversion b coupling V hψ.inversion
  simp only [neg_neg] at hinner hform
  rw [mass_inversion, ← hinner, ← hform] at h
  exact h

namespace CuspParameters

theorem exists_translated_atomic_test_rankOne_gap_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ,
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
      ∀ ψ : Wavefunction, IsTestFunction ψ →
        ((hRad.gap / 2 * coupling) *
            (mass ψ - ‖waveInner (leftState p.b L coupling φ) ψ‖ ^ 2) ≤
          magneticForm p.b coupling (fun x => p.potential (x + displacement L)) ψ -
            atomicGroundEnergy p.b p.potential coupling * mass ψ) ∧
        ((hRad.gap / 2 * coupling) *
            (mass ψ - ‖waveInner (rightState p.b L coupling φ) ψ‖ ^ 2) ≤
          magneticForm p.b coupling (fun x => p.potential (displacement L - x)) ψ -
            atomicGroundEnergy p.b p.potential coupling * mass ψ) := by
  obtain ⟨T, hT, hgap⟩ := exists_atomic_test_rankOne_gap_of_radialData hp hRad hAcore hApot
  refine ⟨T, hT, ?_⟩
  intro coupling hc L φ hφ ψ hψ
  have hleft : ∀ χ : Wavefunction, IsTestFunction χ →
      (hRad.gap / 2 * coupling) *
          (mass χ - ‖waveInner (leftState p.b L coupling φ) χ‖ ^ 2) ≤
        magneticForm p.b coupling (fun x => p.potential (x + displacement L)) χ -
          atomicGroundEnergy p.b p.potential coupling * mass χ := by
    intro χ hχ
    simpa only [leftState, sub_neg_eq_add] using
      test_rankOne_bound_magneticTranslation (hgap coupling hc φ hφ) (-displacement L) hχ
  refine ⟨hleft ψ hψ, ?_⟩
  simpa only [rightState, neg_add_eq_sub] using test_rankOne_bound_inversion hleft hψ

end CuspParameters
end InfiniteZero
