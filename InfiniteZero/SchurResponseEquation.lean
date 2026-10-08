import InfiniteZero.SchurGroundQuantitative

/-!
# The exact uncompressed equation for the normalized Schur response

Subtracting the normalized reference component from the certified eigenvector
defines a correction in the original operator domain. Its equation retains
both the actual residual and the energy-shift term, with their exact signs.
The correction, coefficient and eigenvector all come from the same Schur
certificate; there is no additional choice of phase or eigenfunction.
-/

noncomputable section

namespace InfiniteZero.QuantitativeSchurGroundCertificate

variable {A : L2Space →ₗ.[ℂ] L2Space} {φ : A.domain} {E g : ℝ}
    (q : QuantitativeSchurGroundCertificate A φ E g)

/-- The normalized response belongs to the original unbounded-operator
domain, since both terms in its definition do. -/
def normalizedCorrection : A.domain :=
  q.certificate.normalizedVector -
    (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) • φ

theorem normalizedCorrection_coe :
    (q.normalizedCorrection : L2Space) = (q.certificate.normalizedVector : L2Space) -
      (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        (φ : L2Space) := rfl

set_option maxHeartbeats 800000 in
/-- For a unit reference, this is exactly the negative normalized Schur
correction, with its original compressed-domain witness. -/
theorem normalizedCorrection_eq (hφ : ‖(φ : L2Space)‖ = 1) :
    q.normalizedCorrection =
      -(schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        compressionDomainInclusion A (φ : L2Space) q.correction := by
  rw [normalizedCorrection, q.normalizedVector_eq hφ]
  module

theorem normalizedCorrection_coe_eq (hφ : ‖(φ : L2Space)‖ = 1) :
    (q.normalizedCorrection : L2Space) =
      -(schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) •
        ((q.correction : orthogonalComplement (φ : L2Space)) : L2Space) := by
  rw [q.normalizedCorrection_eq hφ]
  rfl

theorem normalizedCorrection_orthogonal (hφ : ‖(φ : L2Space)‖ = 1) :
    inner ℂ (φ : L2Space) (q.normalizedCorrection : L2Space) = 0 := by
  rw [q.normalizedCorrection_coe_eq hφ, inner_smul_right,
    orthogonalComplement_inner_right, mul_zero]

/-- The uncompressed response equation. No regularity or domain assumptions
on the residual are required: it is a vector of the ambient Hilbert space.
The certified normalized eigenvector is the same one used in the definition. -/
theorem normalizedCorrection_equation {E₀ : ℝ} {r : L2Space}
    (hr : A φ = (E₀ : ℂ) • (φ : L2Space) + r) :
    A q.normalizedCorrection - (E : ℂ) • (q.normalizedCorrection : L2Space) =
      -(schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) • r +
        ((schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) *
          (E - E₀) : ℝ) : ℂ) • (φ : L2Space) := by
  simp only [normalizedCorrection, A.map_sub, A.map_smul,
    q.certificate.normalizedVector_eigenvector, hr,
    Submodule.coe_sub, Submodule.coe_smul, Complex.ofReal_mul, Complex.ofReal_sub]
  module

/-- The same equation recorded as an actual point of the original graph. -/
theorem normalizedCorrection_mem_graph {E₀ : ℝ} {r : L2Space}
    (hr : A φ = (E₀ : ℂ) • (φ : L2Space) + r) :
    ((q.normalizedCorrection : L2Space),
      (E : ℂ) • (q.normalizedCorrection : L2Space) -
        (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) • r +
        ((schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) *
          (E - E₀) : ℝ) : ℂ) • (φ : L2Space)) ∈ A.graph := by
  have heq := q.normalizedCorrection_equation hr
  have hA : A q.normalizedCorrection =
      (E : ℂ) • (q.normalizedCorrection : L2Space) -
        (schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) : ℂ) • r +
        ((schurNormalization (q.correction : orthogonalComplement (φ : L2Space)) *
          (E - E₀) : ℝ) : ℂ) • (φ : L2Space) := by
    rw [sub_eq_iff_eq_add] at heq
    rw [heq]
    module
  exact hA ▸ A.mem_graph q.normalizedCorrection

end InfiniteZero.QuantitativeSchurGroundCertificate
