import InfiniteZero.SecondEnergyTestSpace

/-!
# The second minmax is at most the larger parity bottom

Two nearly minimizing unit tests of opposite parity span a genuine
two-dimensional test space. Its mass and magnetic form are diagonal.
This proves the upper bound directly on the test core, without assuming
that eigenfunctions belong to that core or approximating them jointly.
-/

noncomputable section
open Set
namespace InfiniteZero

theorem finrank_span_even_odd {φ ψ : Wavefunction}
    (hpφ : HasParity true φ) (hpψ : HasParity false ψ) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ ({φ, ψ} : Set Wavefunction)) = 2 := by
  let modes : Fin 2 → Wavefunction := ![φ, ψ]
  have hLI : LinearIndependent ℂ modes := even_odd_linearIndependent hpφ hpψ hφ hψ
  have hrange : Set.range modes = ({φ, ψ} : Set Wavefunction) := by
    ext χ
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [modes]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hrange]
  simpa only [Fintype.card_fin] using finrank_span_eq_card hLI

theorem max_testForms_mem_secondTestUpperBounds {b L coupling : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L)) {φ ψ : Wavefunction}
    (hφ : IsNormalizedTest φ) (hψ : IsNormalizedTest ψ)
    (hpφ : HasParity true φ) (hpψ : HasParity false ψ) :
    max (magneticForm b coupling (doubleWellPotential v L) φ)
      (magneticForm b coupling (doubleWellPotential v L) ψ) ∈
      secondTestUpperBounds b v L coupling := by
  refine ⟨Submodule.span ℂ ({φ, ψ} : Set Wavefunction),
    finrank_span_even_odd hpφ hpψ
      (wavefunction_ne_zero_of_mass_one hφ.2) (wavefunction_ne_zero_of_mass_one hψ.2), ?_, ?_⟩
  · intro χ hχ
    obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.mp hχ
    exact (hφ.1.smul a).add (hψ.1.smul c)
  · intro χ hχ hm
    obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.mp hχ
    have hmass := mass_even_odd_combination hφ.1.memLp hψ.1.memLp hpφ hpψ a c
    rw [hφ.2, hψ.2, mul_one, mul_one, hm] at hmass
    rw [magneticForm_even_odd_combination hV hφ.1 hψ.1 hpφ hpψ]
    let M := max (magneticForm b coupling (doubleWellPotential v L) φ)
      (magneticForm b coupling (doubleWellPotential v L) ψ)
    calc
      _ ≤ ‖a‖ ^ 2 * M + ‖c‖ ^ 2 * M :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))
      _ = M := by rw [← add_mul, ← hmass, one_mul]

theorem secondTestUpperBounds_nonempty {b L coupling : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L))
    (hneEven : ∃ φ : Wavefunction, IsNormalizedTest φ ∧ HasParity true φ)
    (hneOdd : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity false ψ) :
    (secondTestUpperBounds b v L coupling).Nonempty := by
  obtain ⟨φ, hφ, hpφ⟩ := hneEven
  obtain ⟨ψ, hψ, hpψ⟩ := hneOdd
  exact ⟨_, max_testForms_mem_secondTestUpperBounds hV hφ hψ hpφ hpψ⟩

theorem secondEnergy_le_max_testForms {b L coupling : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L)) {B : ℝ}
    (hB : ∀ x, |doubleWellPotential v L x| ≤ B) {φ ψ : Wavefunction}
    (hφ : IsNormalizedTest φ) (hψ : IsNormalizedTest ψ)
    (hpφ : HasParity true φ) (hpψ : HasParity false ψ) :
    secondEnergy b v L coupling ≤
      max (magneticForm b coupling (doubleWellPotential v L) φ)
        (magneticForm b coupling (doubleWellPotential v L) ψ) :=
  csInf_le (secondTestUpperBounds_bddBelow hV hB)
    (max_testForms_mem_secondTestUpperBounds hV hφ hψ hpφ hpψ)

theorem secondEnergy_le_max_parityEnergy {b L coupling : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L)) {B : ℝ}
    (hB : ∀ x, |doubleWellPotential v L x| ≤ B)
    (hneEven : ∃ φ : Wavefunction, IsNormalizedTest φ ∧ HasParity true φ)
    (hneOdd : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity false ψ) :
    secondEnergy b v L coupling ≤
      max (evenEnergy b v L coupling) (oddEnergy b v L coupling) := by
  by_contra! hlt
  let ε := (secondEnergy b v L coupling -
    max (evenEnergy b v L coupling) (oddEnergy b v L coupling)) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have he : parityTestEnergy b coupling (doubleWellPotential v L) true <
      evenEnergy b v L coupling + ε := by
    change evenEnergy b v L coupling < _
    linarith
  have ho : parityTestEnergy b coupling (doubleWellPotential v L) false <
      oddEnergy b v L coupling + ε := by
    change oddEnergy b v L coupling < _
    linarith
  obtain ⟨a, ⟨φ, hφ, hpφ, rfl⟩, hφE⟩ :=
    exists_lt_of_csInf_lt (parityTestFormValues_nonempty b coupling _ true hneEven) he
  obtain ⟨c, ⟨ψ, hψ, hpψ, rfl⟩, hψE⟩ :=
    exists_lt_of_csInf_lt (parityTestFormValues_nonempty b coupling _ false hneOdd) ho
  have hupper := secondEnergy_le_max_testForms (b := b) (coupling := coupling)
    hV hB hφ hψ hpφ hpψ
  have hφlt : magneticForm b coupling (doubleWellPotential v L) φ <
      secondEnergy b v L coupling := by
    have hm := le_max_left (evenEnergy b v L coupling) (oddEnergy b v L coupling)
    dsimp only [ε] at hφE
    linarith
  have hψlt : magneticForm b coupling (doubleWellPotential v L) ψ <
      secondEnergy b v L coupling := by
    have hm := le_max_right (evenEnergy b v L coupling) (oddEnergy b v L coupling)
    dsimp only [ε] at hψE
    linarith
  exact (not_lt_of_ge hupper) (max_lt hφlt hψlt)

end InfiniteZero
