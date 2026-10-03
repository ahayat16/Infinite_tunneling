import InfiniteZero.SecondEnergyParityUpper
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A complement lower bound bounds the second test minmax

The scalar product with one fixed L² vector is a linear functional on
every test subspace. Rank-nullity in a two-dimensional subspace supplies
a nonzero orthogonal test; normalizing it gives the required minmax lower
bound. All function classes and operator energies are the physical ones.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

def testSubmoduleToL2 (F : Submodule ℂ Wavefunction)
    (hTest : ∀ ψ ∈ F, IsTestFunction ψ) : F →ₗ[ℂ] L2Space where
  toFun ψ := (hTest ψ ψ.property).memLp.toLp (ψ : Wavefunction)
  map_add' ψ χ := MemLp.toLp_add (hTest ψ ψ.property).memLp (hTest χ χ.property).memLp
  map_smul' c ψ := MemLp.toLp_const_smul c (hTest ψ ψ.property).memLp

theorem exists_normalized_orthogonal_test_in_submodule (F : Submodule ℂ Wavefunction)
    (hdim : Module.finrank ℂ F = 2) (hTest : ∀ ψ ∈ F, IsTestFunction ψ) (w : L2Space) :
    ∃ ψ ∈ F, ∃ hψ : IsNormalizedTest ψ, inner ℂ w (hψ.1.memLp.toLp ψ) = 0 := by
  letI : FiniteDimensional ℂ F := FiniteDimensional.of_finrank_pos (by omega)
  let ℓ : F →ₗ[ℂ] ℂ := (innerSL ℂ w).toLinearMap.comp (testSubmoduleToL2 F hTest)
  have hker : LinearMap.ker ℓ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa only [Module.finrank_self, hdim] using (by decide : 1 < 2))
  obtain ⟨u, hu, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have horth : inner ℂ w ((hTest u u.property).memLp.toLp (u : Wavefunction)) = 0 := hu
  have hψ := hTest u u.property
  have hm : 0 < mass (u : Wavefunction) :=
    hψ.mass_pos_of_ne_zero (fun h => hune (Subtype.ext h))
  let r : ℝ := (Real.sqrt (mass (u : Wavefunction)))⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  have hnorm : mass ((r : ℂ) • (u : Wavefunction)) = 1 := by
    rw [mass_smul_wavefunction, Complex.norm_real, Real.norm_of_nonneg hr.le]
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  refine ⟨(r : ℂ) • (u : Wavefunction), F.smul_mem _ u.property,
    ⟨hψ.smul _, hnorm⟩, ?_⟩
  rw [MemLp.toLp_const_smul (r : ℂ) hψ.memLp, inner_smul_right, horth, mul_zero]

theorem secondEnergy_lower_of_test_orthogonal {b L coupling E : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L))
    (hneEven : ∃ φ : Wavefunction, IsNormalizedTest φ ∧ HasParity true φ)
    (hneOdd : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity false ψ)
    (w : L2Space)
    (hbound : ∀ (ψ : Wavefunction) (hψ : IsNormalizedTest ψ),
      inner ℂ w (hψ.1.memLp.toLp ψ) = 0 →
      E ≤ magneticForm b coupling (doubleWellPotential v L) ψ) :
    E ≤ secondEnergy b v L coupling := by
  apply le_csInf (secondTestUpperBounds_nonempty hV hneEven hneOdd)
  rintro a ⟨F, hdim, hTest, hupper⟩
  obtain ⟨ψ, hψF, hψ, horth⟩ :=
    exists_normalized_orthogonal_test_in_submodule F hdim hTest w
  exact (hbound ψ hψ horth).trans (hupper ψ hψF hψ.2)

theorem IsMagneticRealization.secondEnergy_lower_of_domain_orthogonal
    {b L coupling E : ℝ} {v : Potential}
    (hA : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hV : Continuous (doubleWellPotential v L))
    (hneEven : ∃ φ : Wavefunction, IsNormalizedTest φ ∧ HasParity true φ)
    (hneOdd : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity false ψ)
    (w : L2Space)
    (hbound : ∀ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      inner ℂ w (u : L2Space) = 0 → E * ‖(u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space)
          (magneticOperator b coupling (doubleWellPotential v L) u)).re) :
    E ≤ secondEnergy b v L coupling := by
  apply secondEnergy_lower_of_test_orthogonal hV hneEven hneOdd w
  intro ψ hψ horth
  have hc : (hψ.1.memLp.toLp ψ,
      (hψ.1.memLp_magneticHamiltonian b coupling hV).toLp
        (magneticHamiltonian b coupling (doubleWellPotential v L) ψ)) ∈
      magneticClosedGraph b coupling (doubleWellPotential v L) := by
    change _ ∈ (magneticClosedGraph b coupling (doubleWellPotential v L) :
      Set (L2Space × L2Space))
    rw [magneticClosedGraph_eq_closure]
    exact subset_closure (hψ.1.mem_magneticTestGraph b coupling hV)
  rw [← hA.graph_eq] at hc
  obtain ⟨u, hu, hAu⟩ := (magneticOperator b coupling (doubleWellPotential v L)).mem_graph_iff.mp hc
  have h := hbound u (by simpa only [hu] using horth)
  rw [hu, hAu, norm_toLp_sq_eq_mass hψ.1.memLp,
    re_inner_toLp_magneticHamiltonian_eq_magneticForm b coupling hV hψ.1
      hψ.1.memLp (hψ.1.memLp_magneticHamiltonian b coupling hV), hψ.2, mul_one] at h
  exact h

end InfiniteZero
