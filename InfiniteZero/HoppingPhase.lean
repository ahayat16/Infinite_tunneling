import InfiniteZero.MagneticModel

/-!
# Independence of the hopping coefficient from the atomic ground-state phase

Both translated modes use the same atomic ground state.  Multiplying that
state by a scalar of norm one therefore cancels pointwise in the hopping
integrand.  This also justifies the use of `canonicalAtomicState` whenever
the normalized atomic ground state is unique up to a constant phase.
-/

noncomputable section

open MeasureTheory

namespace InfiniteZero

/-- Simplicity formulated for the concrete normalized atomic eigenfunctions. -/
def AtomicGroundSimple (b : ℝ) (v : Potential) (coupling : ℝ) : Prop :=
  ∀ φ ψ : Wavefunction,
    IsAtomicGroundState b v coupling φ → IsAtomicGroundState b v coupling ψ →
    ∃ c : ℂ, ‖c‖ = 1 ∧ ψ = c • φ

theorem magneticTranslation_smul (b coupling : ℝ) (a : Plane)
    (c : ℂ) (φ : Wavefunction) :
    magneticTranslation b coupling a (c • φ) = c • magneticTranslation b coupling a φ := by
  funext x
  simp only [magneticTranslation, Pi.smul_apply, smul_eq_mul]
  ac_rfl

theorem leftState_smul (b L coupling : ℝ) (c : ℂ) (φ : Wavefunction) :
    leftState b L coupling (c • φ) = c • leftState b L coupling φ :=
  magneticTranslation_smul b coupling (-displacement L) c φ

theorem rightState_smul (b L coupling : ℝ) (c : ℂ) (φ : Wavefunction) :
    rightState b L coupling (c • φ) = c • rightState b L coupling φ := by
  funext x
  simp only [rightState, leftState_smul, Pi.smul_apply]

/-- A common unit phase cancels before integration; no asymptotic statement
or choice of a continuous phase is used. -/
theorem hopping_smul_unit (b : ℝ) (v : Potential) (L coupling : ℝ)
    (c : ℂ) (hc : ‖c‖ = 1) (φ : Wavefunction) :
    hopping b v L coupling (c • φ) = hopping b v L coupling φ := by
  have hcunit : star c * c = 1 := by
    simpa only [Complex.star_def, hc, one_pow, Complex.ofReal_one] using
      Complex.conj_mul' c
  unfold hopping
  apply congrArg (fun z : ℂ => ((coupling ^ 2 : ℝ) : ℂ) * z)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [leftState_smul, rightState_smul, Pi.smul_apply, smul_eq_mul, star_mul']
    calc
      star c * star (leftState b L coupling φ x) *
          (v (x + displacement L) : ℂ) * (c * rightState b L coupling φ x) =
          (star c * c) * (star (leftState b L coupling φ x) *
            (v (x + displacement L) : ℂ) * rightState b L coupling φ x) := by
        ac_rfl
      _ = _ := by rw [hcunit, one_mul]

/-- The chosen coefficient agrees with that computed from any normalized
atomic ground state, under the explicit simplicity hypothesis. -/
theorem canonicalHopping_eq_hopping (b : ℝ) (v : Potential) (L coupling : ℝ)
    (hsimple : AtomicGroundSimple b v coupling) (φ : Wavefunction)
    (hφ : IsAtomicGroundState b v coupling φ) :
    canonicalHopping b v L coupling = hopping b v L coupling φ := by
  have hcanonical := canonicalAtomicState_spec b v coupling ⟨φ, hφ⟩
  obtain ⟨c, hc, hphase⟩ := hsimple (canonicalAtomicState b v coupling) φ hcanonical hφ
  unfold canonicalHopping
  rw [hphase, hopping_smul_unit b v L coupling c hc]

end InfiniteZero
