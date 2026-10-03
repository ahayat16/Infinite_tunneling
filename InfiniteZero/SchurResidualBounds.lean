import InfiniteZero.SchurEigenvector
import InfiniteZero.AtomicPerturbationDomain

/-!
# Actual residuals control the Schur coupling and diagonal

Projection is a contraction. For a normalized reference vector the scalar
diagonal error is bounded by the same residual. The final specialization
uses the exact core-to-cusp graph identity of the concrete Hamiltonian.
-/

noncomputable section
namespace InfiniteZero

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem complementProjection_reference_zero (φ : H) (hφ : ‖φ‖ = 1) :
    complementProjection φ φ = 0 := by
  apply Subtype.ext
  rw [complementProjection_coe φ hφ]
  simp only [inner_self_eq_norm_sq_to_K, hφ, one_pow, algebraMap.coe_one,
    one_smul, sub_self, ZeroMemClass.coe_zero]

theorem schurCoupling_eq_projected_residual (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (E : ℝ) (r : H)
    (hr : A φ = (E : ℂ) • (φ : H) + r) :
    schurCoupling A φ = complementProjection (φ : H) r := by
  simp only [schurCoupling, hr, map_add, map_smul,
    complementProjection_reference_zero (φ : H) hφ, smul_zero, zero_add]

theorem schurCoupling_norm_le_residual (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (E : ℝ) (r : H)
    (hr : A φ = (E : ℂ) • (φ : H) + r) : ‖schurCoupling A φ‖ ≤ ‖r‖ := by
  rw [schurCoupling_eq_projected_residual A φ hφ E r hr]
  exact (orthogonalComplement (φ : H)).norm_orthogonalProjection_apply_le r

theorem schurDiagonal_eq_reference_add_residual (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (E : ℝ) (r : H)
    (hr : A φ = (E : ℂ) • (φ : H) + r) :
    schurDiagonal A φ = E + (inner ℂ (φ : H) r).re := by
  simp only [schurDiagonal, hr, inner_add_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hφ, one_pow, algebraMap.coe_one, mul_one,
    Complex.add_re, Complex.ofReal_re]

theorem schurDiagonal_sub_reference_le_residual (A : H →ₗ.[ℂ] H) (φ : A.domain)
    (hφ : ‖(φ : H)‖ = 1) (E : ℝ) (r : H)
    (hr : A φ = (E : ℂ) • (φ : H) + r) : |schurDiagonal A φ - E| ≤ ‖r‖ := by
  rw [schurDiagonal_eq_reference_add_residual A φ hφ E r hr, add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans
    (by simpa only [hφ, one_mul] using norm_inner_le_norm (φ : H) r)

end InfiniteZero

namespace InfiniteZero.CuspParameters

theorem exists_atomic_schur_reference_of_core_eigenvector {p : CuspParameters}
    (hp : p.BasicConditions) (coupling : ℝ)
    (hAcore : IsMagneticRealization p.b coupling p.core)
    (hApot : IsMagneticRealization p.b coupling p.potential) {E : ℝ} {u : L2Space}
    (hu : u ∈ operatorEigenspace (magneticOperator p.b coupling p.core) E)
    (hnorm : ‖u‖ = 1) :
    ∃ v : (magneticOperator p.b coupling p.potential).domain,
      (v : L2Space) = u ∧
      ‖schurCoupling (magneticOperator p.b coupling p.potential) v‖ ≤
        ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ ∧
      |schurDiagonal (magneticOperator p.b coupling p.potential) v - E| ≤
        ‖(coupling ^ 2 : ℂ) • atomicPerturbationMul hp u‖ := by
  obtain ⟨v, hv, hAv⟩ := (magneticOperator p.b coupling p.potential).mem_graph_iff.mp
    (atomicOperator_graph_of_core_eigenvector hp coupling hAcore hApot hu)
  have hn : ‖(v : L2Space)‖ = 1 := by simpa only [hv] using hnorm
  have hr : magneticOperator p.b coupling p.potential v =
      (E : ℂ) • (v : L2Space) + (coupling ^ 2 : ℂ) • atomicPerturbationMul hp u := by
    simpa only [hv] using hAv
  exact ⟨v, hv, schurCoupling_norm_le_residual _ v hn E _ hr,
    schurDiagonal_sub_reference_le_residual _ v hn E _ hr⟩

end InfiniteZero.CuspParameters
