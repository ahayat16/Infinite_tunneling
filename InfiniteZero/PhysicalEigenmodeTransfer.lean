import InfiniteZero.ParityGroundCertificate

/-!
# Exact physical eigenspace decompositions from L² spans

Smooth representatives of one or two operator eigenvectors describe all
classical eigenfunctions whenever those vectors span the actual operator
eigenspace. Almost-everywhere equalities are upgraded to pointwise ones by
continuity, as required by `TwoModeRealization`.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem Represents.add {u v : L2Space} {φ ψ : Wavefunction}
    (hu : Represents u φ) (hv : Represents v ψ) : Represents (u + v) (φ + ψ) := by
  filter_upwards [Lp.coeFn_add u v, hu, hv] with x hsum hx hy
  simpa only [Pi.add_apply, hx, hy] using hsum

theorem Represents.eq_of_continuous {u : L2Space} {φ ψ : Wavefunction}
    (hu : Represents u φ) (hv : Represents u ψ) (hφ : Continuous φ) (hψ : Continuous ψ) :
    φ = ψ := Measure.eq_of_ae_eq (hu.symm.trans hv) hφ hψ

theorem IsEigenfunction.add {b coupling E : ℝ} {V : Potential} {φ ψ : Wavefunction}
    (hφ : IsEigenfunction b coupling V E φ) (hψ : IsEigenfunction b coupling V E ψ) :
    IsEigenfunction b coupling V E (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  intro x
  rw [magneticHamiltonian_add b coupling V hφ.1 hψ.1]
  simp only [Pi.add_apply, hφ.2.2, hψ.2.2, mul_add]

theorem IsEigenfunction.smul {b coupling E : ℝ} {V : Potential} {ψ : Wavefunction}
    (hψ : IsEigenfunction b coupling V E ψ) (c : ℂ) :
    IsEigenfunction b coupling V E (c • ψ) := by
  refine ⟨hψ.1.const_smul c, hψ.2.1.const_smul c, ?_⟩
  intro x
  rw [magneticHamiltonian_smul b coupling V hψ.1 c]
  simp only [Pi.smul_apply, smul_eq_mul, hψ.2.2]
  ring

theorem IsMagneticRealization.exists_normalized_eigenfunction_of_vector
    {b coupling E : ℝ} {V : Potential} (hA : IsMagneticRealization b coupling V)
    (u : (magneticOperator b coupling V).domain) (hu : ‖(u : L2Space)‖ = 1)
    (hEig : magneticOperator b coupling V u = (E : ℂ) • (u : L2Space)) :
    ∃ ψ : Wavefunction, IsEigenfunction b coupling V E ψ ∧ mass ψ = 1 ∧
      Represents (u : L2Space) ψ := by
  have hmem : (u : L2Space) ∈ operatorEigenspace (magneticOperator b coupling V) E := by
    rw [mem_operatorEigenspace]
    exact hEig ▸ (magneticOperator b coupling V).mem_graph u
  obtain ⟨ψ, hψ, hrep⟩ := (hA.eigenfunction_iff E _).mp hmem
  refine ⟨ψ, hψ, ?_, hrep⟩
  rw [← hrep.norm_sq_eq_mass, hu, one_pow]

theorem IsMagneticRealization.eigenfunction_one_mode_of_span
    {b coupling E : ℝ} {V : Potential} (hA : IsMagneticRealization b coupling V)
    {u : L2Space} {φ : Wavefunction} (hφ : IsEigenfunction b coupling V E φ)
    (hrep : Represents u φ)
    (hspan : operatorEigenspace (magneticOperator b coupling V) E = Submodule.span ℂ {u}) :
    ∀ ψ, IsEigenfunction b coupling V E ψ ↔ ∃ a : ℂ, a • φ = ψ := by
  intro ψ
  constructor
  · intro hψ
    let w : L2Space := hψ.2.1.toLp ψ
    have hw : Represents w ψ := represents_toLp hψ.2.1
    have hmem := (hA.eigenfunction_iff E w).mpr ⟨ψ, hψ, hw⟩
    rw [hspan] at hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hra : Represents w (a • φ) := ha ▸ hrep.smul a
    exact ⟨a, hra.eq_of_continuous hw (hφ.1.continuous.const_smul a) hψ.1.continuous⟩
  · rintro ⟨a, rfl⟩
    exact hφ.smul a

theorem IsMagneticRealization.eigenfunction_two_modes_of_span
    {b coupling E : ℝ} {V : Potential} (hA : IsMagneticRealization b coupling V)
    {u v : L2Space} {φ χ : Wavefunction}
    (hφ : IsEigenfunction b coupling V E φ) (hχ : IsEigenfunction b coupling V E χ)
    (hu : Represents u φ) (hv : Represents v χ)
    (hspan : operatorEigenspace (magneticOperator b coupling V) E =
      Submodule.span ℂ ({u, v} : Set L2Space)) :
    ∀ ψ, IsEigenfunction b coupling V E ψ ↔ ∃ a c : ℂ, a • φ + c • χ = ψ := by
  intro ψ
  constructor
  · intro hψ
    let w : L2Space := hψ.2.1.toLp ψ
    have hw : Represents w ψ := represents_toLp hψ.2.1
    have hmem := (hA.eigenfunction_iff E w).mpr ⟨ψ, hψ, hw⟩
    rw [hspan] at hmem
    obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp hmem
    have hrac : Represents w (a • φ + c • χ) := hac ▸ (hu.smul a).add (hv.smul c)
    exact ⟨a, c, hrac.eq_of_continuous hw
      ((hφ.1.continuous.const_smul a).add (hχ.1.continuous.const_smul c)) hψ.1.continuous⟩
  · rintro ⟨a, c, rfl⟩
    exact (hφ.smul a).add (hχ.smul c)

end InfiniteZero
