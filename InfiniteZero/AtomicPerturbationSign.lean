import InfiniteZero.AtomicPerturbationDomain
import InfiniteZero.WavefunctionL2Bridge

/-!
# Sign of the actual atomic perturbation

The cusp perturbation is a nonpositive real multiplication operator. Its
self-adjointness and quadratic sign are proved from the actual L² integral.
The exact graph transfer then bounds the full Rayleigh energy of every
radial-core eigenvector, without a spectral assumption on the full potential.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

/-- A bounded real multiplier is self-adjoint on physical complex L². -/
theorem isSelfAdjoint_boundedPotentialMul (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    IsSelfAdjoint (boundedPotentialMul W hW hbound) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_boundedPotentialMul W hW hbound u,
    coe_boundedPotentialMul W hW hbound v] with x hu hv
  calc
    _ = inner ℂ ((W x : ℂ) * u x) (v x) :=
      congrArg (fun z : ℂ => inner ℂ z (v x)) hu
    _ = inner ℂ (u x) ((W x : ℂ) * v x) := by
      change inner ℂ ((W x : ℂ) • u x) (v x) = inner ℂ (u x) ((W x : ℂ) • v x)
      rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    _ = _ := congrArg (inner ℂ (u x)) hv.symm

/-- Exact real quadratic energy of a bounded real multiplication operator. -/
theorem re_inner_boundedPotentialMul_eq_integral (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) (u : L2Space) :
    (inner ℂ u (boundedPotentialMul W hW hbound u)).re =
      ∫ x : Plane, W x * ‖u x‖ ^ 2 := by
  calc
    _ = ∫ x : Plane, (inner ℂ (u x) (boundedPotentialMul W hW hbound u x)).re := by
      rw [L2.inner_def]
      exact (integral_re (L2.integrable_inner (𝕜 := ℂ) u
        (boundedPotentialMul W hW hbound u))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [coe_boundedPotentialMul W hW hbound u] with x hx
      rw [hx]
      change (inner ℂ (u x) ((W x : ℂ) • u x)).re = _
      rw [inner_smul_right, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact congrArg (W x * ·) (norm_sq_eq_re_inner (𝕜 := ℂ) (u x)).symm

theorem re_inner_boundedPotentialMul_nonpos (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) (hWnonpos : ∀ x, W x ≤ 0) (u : L2Space) :
    (inner ℂ u (boundedPotentialMul W hW hbound u)).re ≤ 0 := by
  rw [re_inner_boundedPotentialMul_eq_integral W hW hbound u]
  exact integral_nonpos fun x => mul_nonpos_of_nonpos_of_nonneg (hWnonpos x) (sq_nonneg _)

namespace CuspParameters

theorem atomicPerturbation_nonpos {p : CuspParameters} (hp : p.BasicConditions)
    (x : Plane) : p.atomicPerturbation x ≤ 0 := by
  change p.potential x - p.core x ≤ 0
  simp only [potential, add_sub_cancel_left]
  exact mul_nonpos_of_nonneg_of_nonpos hp.ε_pos.le
    (add_nonpos (cuspPlus_range hp x).2 (cuspMinus_range hp x).2)

theorem isSelfAdjoint_atomicPerturbationMul {p : CuspParameters} (hp : p.BasicConditions) :
    IsSelfAdjoint (atomicPerturbationMul hp) :=
  isSelfAdjoint_boundedPotentialMul p.atomicPerturbation (atomicPerturbation_continuous hp)
    (abs_atomicPerturbation_le_two hp)

theorem re_inner_atomicPerturbationMul_nonpos {p : CuspParameters} (hp : p.BasicConditions)
    (u : L2Space) : (inner ℂ u (atomicPerturbationMul hp u)).re ≤ 0 :=
  re_inner_boundedPotentialMul_nonpos p.atomicPerturbation (atomicPerturbation_continuous hp)
    (abs_atomicPerturbation_le_two hp) (atomicPerturbation_nonpos hp) u

/-- A core eigenvector lies in the full operator domain with Rayleigh energy
no greater than its core energy. No normalization or sign of the coupling is needed. -/
theorem exists_atomicOperator_vector_of_core_eigenvector {p : CuspParameters}
    (hp : p.BasicConditions) (coupling : ℝ)
    (hAcore : IsMagneticRealization p.b coupling p.core)
    (hApot : IsMagneticRealization p.b coupling p.potential) {E : ℝ} {u : L2Space}
    (hu : u ∈ operatorEigenspace (magneticOperator p.b coupling p.core) E) :
    ∃ v : (magneticOperator p.b coupling p.potential).domain,
      (v : L2Space) = u ∧
      (inner ℂ (v : L2Space) (magneticOperator p.b coupling p.potential v)).re ≤
        E * ‖u‖ ^ 2 := by
  have hgraph := atomicOperator_graph_of_core_eigenvector hp coupling hAcore hApot hu
  obtain ⟨v, hv, hAv⟩ := (LinearPMap.mem_graph_iff _).mp hgraph
  refine ⟨v, hv, ?_⟩
  rw [hv, hAv, inner_add_right, inner_smul_right, inner_smul_right, Complex.add_re]
  have hn : (inner ℂ u u).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hnonpos := re_inner_atomicPerturbationMul_nonpos hp u
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hn]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg coupling) hnonpos]

end CuspParameters
end InfiniteZero
