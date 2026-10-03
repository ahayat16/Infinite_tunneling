import InfiniteZero.ParityGroundEigenspaces
import InfiniteZero.PhysicalEigenmodeTransfer

/-!
# Normalized physical parity modes and exact eigenfunction decompositions

Normalizing a sector certificate preserves its gap and reference line.
The resulting unit vectors have smooth physical representatives supplied by
the actual magnetic realization. Global eigenspace spans therefore give
pointwise one-mode or two-mode descriptions with normalized parity modes.
-/

noncomputable section
namespace InfiniteZero.ParityGroundCertificate

variable {A : L2Space →ₗ.[ℂ] L2Space} {even : Bool} {E : ℝ}

/-- The same certificate, with a unit reference vector and unchanged gap. -/
def normalized (c : ParityGroundCertificate A even E) : ParityGroundCertificate A even E where
  vector := c.normalizedVector
  vector_ne_zero := by
    intro hz
    have hn := c.normalizedVector_norm
    rw [hz, norm_zero] at hn
    norm_num at hn
  parity := c.normalizedVector_parity
  eigenvector := c.normalizedVector_eigenvector
  lower_bound := c.lower_bound
  gap := c.gap
  gap_pos := c.gap_pos
  gap_bound := by
    intro u hp hu
    apply c.gap_bound u hp
    have hn : ‖(c.vector : L2Space)‖ ≠ 0 := norm_ne_zero_iff.mpr c.vector_ne_zero
    have hs : (((‖(c.vector : L2Space)‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast inv_ne_zero hn
    rw [normalizedVector, Submodule.coe_smul, inner_smul_left] at hu
    exact (mul_eq_zero.mp hu).resolve_left (by simpa using hs)

@[simp] theorem normalized_vector (c : ParityGroundCertificate A even E) :
    c.normalized.vector = c.normalizedVector := rfl

@[simp] theorem normalized_gap (c : ParityGroundCertificate A even E) :
    c.normalized.gap = c.gap := rfl

theorem normalized_vector_norm (c : ParityGroundCertificate A even E) :
    ‖(c.normalized.vector : L2Space)‖ = 1 := c.normalizedVector_norm

/-- Below the opposite sector bottom, a single normalized physical parity
mode spans every classical eigenfunction at the lower energy. -/
theorem exists_normalized_physical_one_mode
    {b coupling F : ℝ} {V : Potential}
    (c : ParityGroundCertificate (magneticOperator b coupling V) even E)
    (hP : ∀ parity : Bool, ∀ q ∈ (magneticOperator b coupling V).graph,
      ((l2ParitySector parity).starProjection q.1,
        (l2ParitySector parity).starProjection q.2) ∈ (magneticOperator b coupling V).graph)
    (d : ParityGroundCertificate (magneticOperator b coupling V) (!even) F)
    (hEF : E < F) (hA : IsMagneticRealization b coupling V) :
    ∃ φ : Wavefunction, mass φ = 1 ∧ HasParity even φ ∧
      IsEigenfunction b coupling V E φ ∧
      ∀ ψ, IsEigenfunction b coupling V E ψ ↔ ∃ a : ℂ, a • φ = ψ := by
  obtain ⟨φ, hφ, hm, hrep⟩ := hA.exists_normalized_eigenfunction_of_vector
    c.normalizedVector c.normalizedVector_norm c.normalizedVector_eigenvector
  have hp : HasParity even φ :=
    hrep.hasParity_of_continuous hφ.1.continuous c.normalizedVector_parity
  have hspan := c.normalized.global_eigenspace_eq_span_of_lt hP d hEF
  exact ⟨φ, hm, hp, hφ, hA.eigenfunction_one_mode_of_span hφ hrep hspan⟩

/-- At a crossing, two normalized modes of opposite parity span exactly
all classical eigenfunctions; the identity of functions is pointwise. -/
theorem exists_normalized_physical_two_modes
    {b coupling : ℝ} {V : Potential}
    (c : ParityGroundCertificate (magneticOperator b coupling V) even E)
    (hP : ∀ parity : Bool, ∀ q ∈ (magneticOperator b coupling V).graph,
      ((l2ParitySector parity).starProjection q.1,
        (l2ParitySector parity).starProjection q.2) ∈ (magneticOperator b coupling V).graph)
    (d : ParityGroundCertificate (magneticOperator b coupling V) (!even) E)
    (hA : IsMagneticRealization b coupling V) :
    ∃ φ χ : Wavefunction, mass φ = 1 ∧ mass χ = 1 ∧
      HasParity even φ ∧ HasParity (!even) χ ∧
      IsEigenfunction b coupling V E φ ∧ IsEigenfunction b coupling V E χ ∧
      ∀ ψ, IsEigenfunction b coupling V E ψ ↔
        ∃ a z : ℂ, a • φ + z • χ = ψ := by
  obtain ⟨φ, hφ, hmφ, hrepφ⟩ := hA.exists_normalized_eigenfunction_of_vector
    c.normalizedVector c.normalizedVector_norm c.normalizedVector_eigenvector
  obtain ⟨χ, hχ, hmχ, hrepχ⟩ := hA.exists_normalized_eigenfunction_of_vector
    d.normalizedVector d.normalizedVector_norm d.normalizedVector_eigenvector
  have hpφ : HasParity even φ :=
    hrepφ.hasParity_of_continuous hφ.1.continuous c.normalizedVector_parity
  have hpχ : HasParity (!even) χ :=
    hrepχ.hasParity_of_continuous hχ.1.continuous d.normalizedVector_parity
  have hspan := c.normalized.global_eigenspace_eq_span_pair hP d.normalized
  exact ⟨φ, χ, hmφ, hmχ, hpφ, hpχ, hφ, hχ,
    hA.eigenfunction_two_modes_of_span hφ hχ hrepφ hrepχ hspan⟩

end InfiniteZero.ParityGroundCertificate
