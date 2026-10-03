import InfiniteZero.MagneticModel

/-!
# Algebraic multiplicity and parity from spectral mode decompositions

The analytic task is to characterize all ground eigenfunctions by one or two
modes.  Once such a characterization is supplied, this file proves the exact
dimension; it does not take the dimension itself as an assumption.
-/

noncomputable section

namespace InfiniteZero

theorem wavefunction_ne_zero_of_mass_one {ψ : Wavefunction} (h : mass ψ = 1) : ψ ≠ 0 := by
  intro hz
  simp [hz, mass] at h

/-- Opposite parities separate any two nonzero functions, without requiring
an inner product or an orthogonality integral. -/
theorem even_odd_linearIndependent {ψEven ψOdd : Wavefunction}
    (hEven : HasParity true ψEven) (hOdd : HasParity false ψOdd)
    (hneEven : ψEven ≠ 0) (hneOdd : ψOdd ≠ 0) :
    LinearIndependent ℂ ![ψEven, ψOdd] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have he : a • ψEven = 0 := by
    funext x
    have hp := congrFun hab x
    have hm := congrFun hab (-x)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hp hm ⊢
    have hev : ψEven (-x) = ψEven x := hEven x
    have hov : ψOdd (-x) = -ψOdd x := hOdd x
    rw [hev, hov] at hm
    linear_combination (1 / 2 : ℂ) * hp + (1 / 2 : ℂ) * hm
  have ho : b • ψOdd = 0 := by simpa only [he, zero_add] using hab
  exact ⟨(smul_eq_zero.mp he).resolve_right hneEven,
    (smul_eq_zero.mp ho).resolve_right hneOdd⟩

/-- Exactly two spectral modes of opposite parity give multiplicity exactly two.
The hypothesis is an exact description of all classical `L²` ground solutions. -/
theorem groundSpaceExactlyTwo_of_two_modes {b L coupling : ℝ} {v : Potential}
    (ψEven ψOdd : Wavefunction)
    (hmEven : mass ψEven = 1) (hmOdd : mass ψOdd = 1)
    (hpEven : HasParity true ψEven) (hpOdd : HasParity false ψOdd)
    (hdecomp : ∀ ψ, IsDoubleEigenfunction b v L coupling (groundEnergy b v L coupling) ψ ↔
      ∃ a c : ℂ, a • ψEven + c • ψOdd = ψ) :
    GroundSpaceExactlyTwo b v L coupling := by
  let G := Submodule.span ℂ ({ψEven, ψOdd} : Set Wavefunction)
  have hG : IsGroundEigenspace b v L coupling G := by
    intro ψ
    rw [hdecomp]
    exact Submodule.mem_span_pair
  let modes : Fin 2 → Wavefunction := ![ψEven, ψOdd]
  have hLI : LinearIndependent ℂ modes := even_odd_linearIndependent hpEven hpOdd
    (wavefunction_ne_zero_of_mass_one hmEven) (wavefunction_ne_zero_of_mass_one hmOdd)
  have hrange : Set.range modes = ({ψEven, ψOdd} : Set Wavefunction) := by
    ext ψ
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [modes]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hdim : Module.finrank ℂ G = 2 := by
    change Module.finrank ℂ (Submodule.span ℂ ({ψEven, ψOdd} : Set Wavefunction)) = 2
    rw [← hrange]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hLI
  refine ⟨G, hG, hdim, ψEven, ψOdd, ?_, ?_, hmEven, hmOdd, hpEven, hpOdd⟩
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)

/-- A one-mode description of the full ground space yields simplicity with
the supplied parity. This is the algebra used away from an exact crossing. -/
theorem simpleGroundParity_of_one_mode {b L coupling : ℝ} {v : Potential}
    (even : Bool) (ψ : Wavefunction) (hm : mass ψ = 1) (hp : HasParity even ψ)
    (hdecomp : ∀ χ, IsDoubleEigenfunction b v L coupling (groundEnergy b v L coupling) χ ↔
      ∃ a : ℂ, a • ψ = χ) :
    SimpleGroundParity b v L coupling even := by
  let G := Submodule.span ℂ ({ψ} : Set Wavefunction)
  have hG : IsGroundEigenspace b v L coupling G := by
    intro χ
    rw [hdecomp]
    exact Submodule.mem_span_singleton
  refine ⟨G, hG, ?_, ψ, Submodule.subset_span (by simp), hm, hp⟩
  exact finrank_span_singleton (wavefunction_ne_zero_of_mass_one hm)

/-- Analytic mode decomposition of the lowest doublet. No finrank or simplicity
conclusion is assumed: these are proved by the algebra above.

The existence and completeness of the mode descriptions are still substantial
spectral obligations, obtained in the manuscript from the parity Schur theorem.
-/
structure TwoModeRealization (b : ℝ) (v : Potential) (L threshold : ℝ) : Prop where
  ordered_ground : ∀ coupling, threshold ≤ coupling →
    groundEnergy b v L coupling = min (evenEnergy b v L coupling) (oddEnergy b v L coupling)
  ordered_second : ∀ coupling, threshold ≤ coupling →
    secondEnergy b v L coupling = max (evenEnergy b v L coupling) (oddEnergy b v L coupling)
  crossing_modes : ∀ coupling, threshold ≤ coupling →
    evenEnergy b v L coupling = oddEnergy b v L coupling →
    ∃ ψEven ψOdd : Wavefunction,
      mass ψEven = 1 ∧ mass ψOdd = 1 ∧
      HasParity true ψEven ∧ HasParity false ψOdd ∧
      ∀ ψ, IsDoubleEigenfunction b v L coupling (groundEnergy b v L coupling) ψ ↔
        ∃ a c : ℂ, a • ψEven + c • ψOdd = ψ
  even_mode : ∀ coupling, threshold ≤ coupling →
    evenEnergy b v L coupling < oddEnergy b v L coupling →
    ∃ ψ : Wavefunction, mass ψ = 1 ∧ HasParity true ψ ∧
      ∀ χ, IsDoubleEigenfunction b v L coupling (groundEnergy b v L coupling) χ ↔
        ∃ a : ℂ, a • ψ = χ
  odd_mode : ∀ coupling, threshold ≤ coupling →
    oddEnergy b v L coupling < evenEnergy b v L coupling →
    ∃ ψ : Wavefunction, mass ψ = 1 ∧ HasParity false ψ ∧
      ∀ χ, IsDoubleEigenfunction b v L coupling (groundEnergy b v L coupling) χ ↔
        ∃ a : ℂ, a • ψ = χ

/-- Exact dimension and parity now follow from the analytic mode descriptions. -/
theorem TwoModeRealization.toSpectralRealization {b L threshold : ℝ} {v : Potential}
    (h : TwoModeRealization b v L threshold) : SpectralRealization b v L threshold where
  ordered_ground := h.ordered_ground
  ordered_second := h.ordered_second
  crossing coupling hc heq := by
    obtain ⟨ψEven, ψOdd, hmEven, hmOdd, hpEven, hpOdd, hdecomp⟩ :=
      h.crossing_modes coupling hc heq
    exact groundSpaceExactlyTwo_of_two_modes ψEven ψOdd hmEven hmOdd hpEven hpOdd hdecomp
  even_lower coupling hc hlt := by
    obtain ⟨ψ, hm, hp, hdecomp⟩ := h.even_mode coupling hc hlt
    exact simpleGroundParity_of_one_mode true ψ hm hp hdecomp
  odd_lower coupling hc hlt := by
    obtain ⟨ψ, hm, hp, hdecomp⟩ := h.odd_mode coupling hc hlt
    exact simpleGroundParity_of_one_mode false ψ hm hp hdecomp

end InfiniteZero
