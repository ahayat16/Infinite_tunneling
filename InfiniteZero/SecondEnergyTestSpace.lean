import InfiniteZero.ParityTestFormOrthogonality
import InfiniteZero.ParityEnergyContinuity
import InfiniteZero.GroundSpaceAlgebra

/-!
# Normalized vectors and lower bounds for the second test minmax

Every nonzero smooth test has positive mass. Consequently every test
subspace of positive finite rank contains a unit test, so a lower form
bound bounds below the actual set defining the second minmax.
-/

noncomputable section
open Set
namespace InfiniteZero

theorem IsTestFunction.mass_pos_of_ne_zero {ψ : Wavefunction}
    (hψ : IsTestFunction ψ) (hne : ψ ≠ 0) : 0 < mass ψ := by
  exact lt_of_le_of_ne (mass_nonneg ψ) (Ne.symm fun h => hne (hψ.eq_zero_of_mass_eq_zero h))

theorem exists_normalized_test_in_submodule (F : Submodule ℂ Wavefunction)
    (hdim : 0 < Module.finrank ℂ F)
    (hTest : ∀ ψ ∈ F, IsTestFunction ψ) :
    ∃ ψ ∈ F, IsNormalizedTest ψ := by
  letI : Nontrivial F := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨u, hu⟩ := exists_ne (0 : F)
  have hune : (u : Wavefunction) ≠ 0 := by
    intro h
    exact hu (Subtype.ext h)
  have hψ := hTest u u.property
  have hm := hψ.mass_pos_of_ne_zero hune
  let r : ℝ := (Real.sqrt (mass (u : Wavefunction)))⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  refine ⟨(r : ℂ) • (u : Wavefunction), F.smul_mem _ u.property, hψ.smul _, ?_⟩
  rw [mass_smul_wavefunction, Complex.norm_real, Real.norm_of_nonneg hr.le]
  dsimp only [r]
  rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']

def secondTestUpperBounds (b : ℝ) (v : Potential) (L coupling : ℝ) : Set ℝ :=
  {E | ∃ F : Submodule ℂ Wavefunction,
    Module.finrank ℂ F = 2 ∧
    (∀ ψ ∈ F, IsTestFunction ψ) ∧
    (∀ ψ ∈ F, mass ψ = 1 → magneticForm b coupling (doubleWellPotential v L) ψ ≤ E)}

theorem secondTestUpperBounds_bddBelow_of_test_lower {b L coupling C : ℝ} {v : Potential}
    (hbound : ∀ ψ : Wavefunction, IsNormalizedTest ψ →
      C ≤ magneticForm b coupling (doubleWellPotential v L) ψ) :
    BddBelow (secondTestUpperBounds b v L coupling) := by
  refine ⟨C, ?_⟩
  rintro E ⟨F, hdim, hTest, hE⟩
  obtain ⟨ψ, hψF, hψ⟩ := exists_normalized_test_in_submodule F (by omega) hTest
  exact (hbound ψ hψ).trans (hE ψ hψF hψ.2)

theorem secondTestUpperBounds_bddBelow {b L coupling : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L)) {B : ℝ}
    (hB : ∀ x, |doubleWellPotential v L x| ≤ B) :
    BddBelow (secondTestUpperBounds b v L coupling) := by
  apply secondTestUpperBounds_bddBelow_of_test_lower (C := -(coupling ^ 2 * B))
  intro ψ hψ
  have h := abs_magneticForm_sub_le (W := 0) b coupling hV continuous_const
    hψ.1 (δ := B) (fun x => by simpa only [Pi.zero_apply, sub_zero] using hB x)
  rw [hψ.2, mul_one] at h
  have hfree := magneticForm_zero_potential_nonneg b coupling ψ
  have hlo := (abs_le.mp h).1
  linarith

end InfiniteZero
