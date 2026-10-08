import InfiniteZero.OperatorBridge
import InfiniteZero.MagneticIntegrationByParts

/-!
# The actual test graph is a complex subspace

The differential expression is linear on smooth functions. Its genuine test
function graph is therefore already a subspace, so taking its linear span in
the canonical closed graph adds no points. Continuity of the potential also
ensures that every test function and its Hamiltonian belong to physical L².
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace InfiniteZero

theorem isTestFunction_zero : IsTestFunction (0 : Wavefunction) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩

theorem IsTestFunction.add {ψ χ : Wavefunction} (hψ : IsTestFunction ψ)
    (hχ : IsTestFunction χ) : IsTestFunction (ψ + χ) :=
  ⟨hψ.1.add hχ.1, hψ.2.add hχ.2⟩

theorem IsTestFunction.smul {ψ : Wavefunction} (hψ : IsTestFunction ψ) (c : ℂ) :
    IsTestFunction (c • ψ) :=
  ⟨hψ.1.const_smul c, hψ.2.comp_left (g := fun z : ℂ => c • z) (by simp)⟩

theorem IsTestFunction.memLp {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2

theorem partialDerivative_add (i : Fin 2) {ψ χ : Wavefunction}
    (hψ : Differentiable ℝ ψ) (hχ : Differentiable ℝ χ) :
    partialDerivative i (ψ + χ) = partialDerivative i ψ + partialDerivative i χ := by
  funext x
  change fderiv ℝ (fun y => ψ y + χ y) x (coordinateVector i) = _
  rw [fderiv_fun_add (hψ x) (hχ x)]
  rfl

theorem partialDerivative_smul (i : Fin 2) {ψ : Wavefunction}
    (hψ : Differentiable ℝ ψ) (c : ℂ) :
    partialDerivative i (c • ψ) = c • partialDerivative i ψ := by
  funext x
  unfold partialDerivative
  rw [fderiv_const_smul (hψ x) c]
  rfl

theorem covariantDerivative_add (b coupling : ℝ) (i : Fin 2) {ψ χ : Wavefunction}
    (hψ : Differentiable ℝ ψ) (hχ : Differentiable ℝ χ) :
    covariantDerivative b coupling i (ψ + χ) =
      covariantDerivative b coupling i ψ + covariantDerivative b coupling i χ := by
  funext x
  simp only [covariantDerivative, partialDerivative_add i hψ hχ, Pi.add_apply]
  ring

theorem covariantDerivative_smul (b coupling : ℝ) (i : Fin 2) {ψ : Wavefunction}
    (hψ : Differentiable ℝ ψ) (c : ℂ) :
    covariantDerivative b coupling i (c • ψ) = c • covariantDerivative b coupling i ψ := by
  funext x
  simp only [covariantDerivative, partialDerivative_smul i hψ c, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem covariantDerivative_zero (b coupling : ℝ) (i : Fin 2) :
    covariantDerivative b coupling i 0 = 0 := by
  ext x
  simp [covariantDerivative, partialDerivative]

@[simp] theorem magneticHamiltonian_zero (b coupling : ℝ) (V : Potential) :
    magneticHamiltonian b coupling V 0 = 0 := by
  ext x
  simp [magneticHamiltonian]

theorem magneticHamiltonian_add (b coupling : ℝ) (V : Potential) {ψ χ : Wavefunction}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) :
    magneticHamiltonian b coupling V (ψ + χ) =
      magneticHamiltonian b coupling V ψ + magneticHamiltonian b coupling V χ := by
  have hD (i : Fin 2) :
      covariantDerivative b coupling i (covariantDerivative b coupling i (ψ + χ)) =
        covariantDerivative b coupling i (covariantDerivative b coupling i ψ) +
          covariantDerivative b coupling i (covariantDerivative b coupling i χ) := by
    rw [covariantDerivative_add b coupling i (hψ.differentiable (by simp))
      (hχ.differentiable (by simp)), covariantDerivative_add b coupling i
      ((contDiff_covariantDerivative b coupling i hψ).differentiable (by simp))
      ((contDiff_covariantDerivative b coupling i hχ).differentiable (by simp))]
  funext x
  simp only [magneticHamiltonian, hD, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem magneticHamiltonian_smul (b coupling : ℝ) (V : Potential) {ψ : Wavefunction}
    (hψ : ContDiff ℝ ∞ ψ) (c : ℂ) :
    magneticHamiltonian b coupling V (c • ψ) = c • magneticHamiltonian b coupling V ψ := by
  have hD (i : Fin 2) :
      covariantDerivative b coupling i (covariantDerivative b coupling i (c • ψ)) =
        c • covariantDerivative b coupling i (covariantDerivative b coupling i ψ) := by
    rw [covariantDerivative_smul b coupling i (hψ.differentiable (by simp)),
      covariantDerivative_smul b coupling i
      ((contDiff_covariantDerivative b coupling i hψ).differentiable (by simp))]
  funext x
  simp only [magneticHamiltonian, hD, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem IsTestFunction.continuous_magneticHamiltonian (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hψ : IsTestFunction ψ) (hV : Continuous V) :
    Continuous (magneticHamiltonian b coupling V ψ) := by
  apply Continuous.add
  · exact continuous_finsetSum _ fun i _ =>
      ((hψ.covariantDerivative b coupling i).covariantDerivative b coupling i).1.continuous
  · exact (Complex.continuous_ofReal.comp (continuous_const.mul hV)).mul hψ.1.continuous

theorem IsTestFunction.hasCompactSupport_magneticHamiltonian (b coupling : ℝ)
    (V : Potential) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    HasCompactSupport (magneticHamiltonian b coupling V ψ) := by
  have hD (i : Fin 2) :=
    ((hψ.covariantDerivative b coupling i).covariantDerivative b coupling i).2
  have hpot : HasCompactSupport
      (fun x => ((coupling ^ 2 * V x : ℝ) : ℂ) * ψ x) := hψ.2.mul_left
  change HasCompactSupport (fun x =>
    (∑ i : Fin 2, InfiniteZero.covariantDerivative b coupling i
      (InfiniteZero.covariantDerivative b coupling i ψ) x) +
      ((coupling ^ 2 * V x : ℝ) : ℂ) * ψ x)
  simpa only [Fin.sum_univ_two, Pi.add_apply] using ((hD 0).add (hD 1)).add hpot

theorem IsTestFunction.memLp_magneticHamiltonian (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hψ : IsTestFunction ψ) (hV : Continuous V) :
    MemLp (magneticHamiltonian b coupling V ψ) 2 volume :=
  (hψ.continuous_magneticHamiltonian b coupling hV).memLp_of_hasCompactSupport
    (hψ.hasCompactSupport_magneticHamiltonian b coupling V)

/-- Every actual test function supplies a point in the original graph. -/
theorem IsTestFunction.mem_magneticTestGraph (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hψ : IsTestFunction ψ) (hV : Continuous V) :
    (hψ.memLp.toLp ψ,
      (hψ.memLp_magneticHamiltonian b coupling hV).toLp (magneticHamiltonian b coupling V ψ)) ∈
      magneticTestGraph b coupling V :=
  ⟨ψ, hψ, hψ.memLp, hψ.memLp_magneticHamiltonian b coupling hV, rfl, rfl⟩

/-- Linearity of the graph needs no regularity of the potential: membership
already includes the necessary two `L²` conditions. -/
def magneticTestGraphSubmodule (b coupling : ℝ) (V : Potential) :
    Submodule ℂ (L2Space × L2Space) where
  carrier := magneticTestGraph b coupling V
  zero_mem' := by
    refine ⟨0, isTestFunction_zero, MemLp.zero, ?_⟩
    have hzero : MemLp (magneticHamiltonian b coupling V 0) 2 volume := by simp
    exact ⟨hzero, by simp, by simp⟩
  add_mem' := by
    rintro q₁ q₂ ⟨ψ, hψ, hψL, hHψ, hq₁, hq₁'⟩ ⟨χ, hχ, hχL, hHχ, hq₂, hq₂'⟩
    have hH : MemLp (magneticHamiltonian b coupling V (ψ + χ)) 2 volume := by
      rw [magneticHamiltonian_add b coupling V hψ.1 hχ.1]
      exact hHψ.add hHχ
    refine ⟨ψ + χ, hψ.add hχ, hψL.add hχL, hH, ?_, ?_⟩
    · simpa only [Prod.fst_add, hq₁, hq₂] using (hψL.toLp_add hχL).symm
    · simp only [Prod.snd_add, hq₁', hq₂']
      rw [← hHψ.toLp_add hHχ]
      exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x =>
        congrFun (magneticHamiltonian_add b coupling V hψ.1 hχ.1) x)).symm
  smul_mem' := by
    rintro c q ⟨ψ, hψ, hψL, hHψ, hq, hq'⟩
    have hH : MemLp (magneticHamiltonian b coupling V (c • ψ)) 2 volume := by
      rw [magneticHamiltonian_smul b coupling V hψ.1 c]
      exact hHψ.const_smul c
    refine ⟨c • ψ, hψ.smul c, hψL.const_smul c, hH, ?_, ?_⟩
    · simpa only [Prod.smul_fst, hq] using (hψL.toLp_const_smul c).symm
    · simp only [Prod.smul_snd, hq']
      rw [← hHψ.toLp_const_smul c]
      exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x =>
        congrFun (magneticHamiltonian_smul b coupling V hψ.1 c) x)).symm

@[simp] theorem coe_magneticTestGraphSubmodule (b coupling : ℝ) (V : Potential) :
    (magneticTestGraphSubmodule b coupling V : Set (L2Space × L2Space)) =
      magneticTestGraph b coupling V := rfl

/-- The span used in the canonical operator definition adds no graph points. -/
theorem span_magneticTestGraph (b coupling : ℝ) (V : Potential) :
    Submodule.span ℂ (magneticTestGraph b coupling V) = magneticTestGraphSubmodule b coupling V := by
  exact Submodule.span_eq (magneticTestGraphSubmodule b coupling V)

/-- The canonical closed graph is the ordinary closure of the actual test graph. -/
theorem magneticClosedGraph_eq_closure (b coupling : ℝ) (V : Potential) :
    (magneticClosedGraph b coupling V : Set (L2Space × L2Space)) =
      closure (magneticTestGraph b coupling V) := by
  rw [magneticClosedGraph, span_magneticTestGraph, Submodule.topologicalClosure_coe]
  rfl

end InfiniteZero
