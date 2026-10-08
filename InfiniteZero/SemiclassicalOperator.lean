import InfiniteZero.OperatorSecondMinmax
import Mathlib.Data.Real.Pointwise

/-!
# Semiclassical scaling of the magnetic operator and its min-max levels

Multiplication of the operator by a positive real scalar multiplies both
variational levels by that scalar, on the same operator domain. The
semiclassical unit-field operator is `h² H(1/h)`, so its energy levels are
in the normalization used by the radial harmonic approximation theorem.
-/

noncomputable section
open scoped Pointwise

namespace InfiniteZero

/-- Multiplying an operator by a real scalar multiplies its real quadratic
energy by the same scalar. Its domain is unchanged definitionally. -/
theorem operatorEnergy_real_smul (A : L2Space →ₗ.[ℂ] L2Space) (c : ℝ)
    (u : A.domain) :
    (inner ℂ (u : L2Space) (((c : ℂ) • A) u)).re =
      c * (inner ℂ (u : L2Space) (A u)).re := by
  rw [LinearPMap.smul_apply, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Nonnegative real scaling commutes with the first variational level,
including the empty and unbounded cases covered by the real infimum. -/
theorem operatorVariationalBottom_real_smul (A : L2Space →ₗ.[ℂ] L2Space)
    {c : ℝ} (hc : 0 ≤ c) :
    operatorVariationalBottom ((c : ℂ) • A) = c * operatorVariationalBottom A := by
  have hset : {E : ℝ | ∃ u : (((c : ℂ) • A).domain), ‖(u : L2Space)‖ = 1 ∧
      (inner ℂ (u : L2Space) (((c : ℂ) • A) u)).re = E} =
      c • {E : ℝ | ∃ u : A.domain, ‖(u : L2Space)‖ = 1 ∧
        (inner ℂ (u : L2Space) (A u)).re = E} := by
    ext E
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Set.mem_smul_set.mpr ⟨(inner ℂ (u : L2Space) (A u)).re,
        ⟨u, hu, rfl⟩, (operatorEnergy_real_smul A c u).symm⟩
    · intro hE
      obtain ⟨r, ⟨u, hu, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hE
      exact ⟨u, hu, operatorEnergy_real_smul A c u⟩
  unfold operatorVariationalBottom
  rw [hset, Real.sInf_smul_of_nonneg hc]
  rfl

/-- Positive real scaling acts on the complete set of second-level upper
bounds, while preserving the admissible two-dimensional domain subspaces. -/
theorem operatorSecondUpperBounds_real_smul (A : L2Space →ₗ.[ℂ] L2Space)
    {c : ℝ} (hc : 0 < c) :
    operatorSecondUpperBounds ((c : ℂ) • A) = c • operatorSecondUpperBounds A := by
  ext E
  constructor
  · rintro ⟨F, hF, hbound⟩
    refine Set.mem_smul_set.mpr ⟨E / c, ⟨F, hF, ?_⟩, ?_⟩
    · intro u hu hnorm
      apply (le_div_iff₀ hc).mpr
      have h := hbound u hu hnorm
      rw [operatorEnergy_real_smul] at h
      simpa only [mul_comm] using h
    · change c * (E / c) = E
      field_simp
  · intro hE
    obtain ⟨r, ⟨F, hF, hbound⟩, rfl⟩ := Set.mem_smul_set.mp hE
    refine ⟨F, hF, ?_⟩
    intro u hu hnorm
    exact (operatorEnergy_real_smul A c u).trans_le
      (mul_le_mul_of_nonneg_left (hbound u hu hnorm) hc.le)

/-- Positive real scaling commutes with the second operator min-max. -/
theorem operatorSecondMinmax_real_smul (A : L2Space →ₗ.[ℂ] L2Space)
    {c : ℝ} (hc : 0 < c) :
    operatorSecondMinmax ((c : ℂ) • A) = c * operatorSecondMinmax A := by
  unfold operatorSecondMinmax
  rw [operatorSecondUpperBounds_real_smul A hc, Real.sInf_smul_of_nonneg hc.le]
  rfl

/-- For nonzero `h`, the unit-field semiclassical operator `(-ih∇ - A)² + V`,
defined on `L²` by scaling the closed unscaled operator, with the same domain. -/
def semiclassicalMagneticOperator (V : Potential) (h : ℝ) : L2Space →ₗ.[ℂ] L2Space :=
  ((h ^ 2 : ℝ) : ℂ) • magneticOperator 1 h⁻¹ V

/-- Exact conversion of the first level to semiclassical energy units. -/
theorem semiclassicalMagneticOperator_variationalBottom (V : Potential) (h : ℝ) :
    operatorVariationalBottom (semiclassicalMagneticOperator V h) =
      h ^ 2 * operatorVariationalBottom (magneticOperator 1 h⁻¹ V) :=
  operatorVariationalBottom_real_smul _ (sq_nonneg h)

/-- Exact conversion of the second level to semiclassical energy units. -/
theorem semiclassicalMagneticOperator_secondMinmax (V : Potential)
    {h : ℝ} (hh : h ≠ 0) :
    operatorSecondMinmax (semiclassicalMagneticOperator V h) =
      h ^ 2 * operatorSecondMinmax (magneticOperator 1 h⁻¹ V) :=
  operatorSecondMinmax_real_smul _ (sq_pos_of_ne_zero hh)

/-- A ground eigenvector of a positively scaled operator is the same vector
at the ground energy of the unscaled operator. -/
theorem operatorVariationalBottom_eigenvector_of_real_smul
    (A : L2Space →ₗ.[ℂ] L2Space) {c : ℝ} (hc : 0 < c)
    (v : A.domain)
    (hv : ((c : ℂ) • A) v =
      (operatorVariationalBottom ((c : ℂ) • A) : ℂ) • (v : L2Space)) :
    A v = (operatorVariationalBottom A : ℂ) • (v : L2Space) := by
  rw [LinearPMap.smul_apply, operatorVariationalBottom_real_smul A hc.le,
    Complex.ofReal_mul, mul_smul] at hv
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  exact smul_right_injective L2Space hcn hv

/-- Semiclassical ground eigenvectors retain their normalization and vector
when read in the unscaled operator domain. -/
theorem semiclassicalMagneticOperator_ground_eigenvector
    (V : Potential) {h : ℝ} (hh : h ≠ 0)
    (v : (semiclassicalMagneticOperator V h).domain)
    (hv : semiclassicalMagneticOperator V h v =
      (operatorVariationalBottom (semiclassicalMagneticOperator V h) : ℂ) •
        (v : L2Space)) :
    magneticOperator 1 h⁻¹ V v =
      (operatorVariationalBottom (magneticOperator 1 h⁻¹ V) : ℂ) • (v : L2Space) :=
  operatorVariationalBottom_eigenvector_of_real_smul
    (magneticOperator 1 h⁻¹ V) (sq_pos_of_ne_zero hh) v hv

end InfiniteZero
