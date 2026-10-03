import InfiniteZero.AtomicSchurReference
import InfiniteZero.SchurGroundQuantitative
import InfiniteZero.AtomicExponentialWeightOps

/-!
# One forcing factor controls the actual atomic energy shift

The scalar equation retained by the same Schur certificate gives a bound
linear in the true core-to-full residual, with coefficient `1 + ‖ζ‖`.
The positive normalization bound `c ≥ 1/2` makes this coefficient at most
three. Rescaling removes the factor `λ²` of the non-rescaled residual.
Neither a small residual nor an asymptotic estimate is assumed.
-/

noncomputable section
open Set

namespace InfiniteZero

/-- A lower normalization bound directly controls the correction, without
using its equation or assuming smallness of the forcing. -/
theorem norm_sq_le_three_of_half_le_schurNormalization
    {H : Type*} [NormedAddCommGroup H] {ζ : H}
    (hc : (1 / 2 : ℝ) ≤ schurNormalization ζ) : ‖ζ‖ ^ 2 ≤ 3 := by
  have hs : 0 < Real.sqrt (1 + ‖ζ‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hc hs.le
  have hcancel : schurNormalization ζ * Real.sqrt (1 + ‖ζ‖ ^ 2) = 1 :=
    inv_mul_cancel₀ hs.ne'
  rw [hcancel] at hmul
  have hsle : Real.sqrt (1 + ‖ζ‖ ^ 2) ≤ 2 := by linarith
  have hsq := (sq_le_sq₀ hs.le (by norm_num : (0 : ℝ) ≤ 2)).mpr hsle
  rw [Real.sq_sqrt (by positivity)] at hsq
  linarith

namespace AtomicSchurReference

variable {p : CuspParameters} {hp : p.BasicConditions} {coupling gap E : ℝ}
    (s : AtomicSchurReference p hp coupling gap)
    (q : QuantitativeSchurGroundCertificate
      (magneticOperator p.b coupling p.potential) s.vector E gap)

/-- The exact scalar Schur equation yields a single residual factor.
The energy and correction belong to the given certificate for the given
core reference; no independent choice of state is made. -/
theorem energy_shift_le_forcing :
    |E - atomicGroundEnergy p.b p.core coupling| ≤
      (1 + ‖(q.correction : orthogonalComplement (s.vector : L2Space))‖) *
        ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp
          (s.vector : L2Space)‖ := by
  have hs := congrArg Complex.re q.scalar_equation
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hs
  have heq : schurDiagonal (magneticOperator p.b coupling p.potential) s.vector - E =
      (inner ℂ (schurCoupling (magneticOperator p.b coupling p.potential) s.vector)
        (q.correction : orthogonalComplement (s.vector : L2Space))).re := by
    dsimp only [schurDiagonal]
    linarith only [hs]
  have hinner : schurDiagonal (magneticOperator p.b coupling p.potential) s.vector - E ≤
      ‖schurCoupling (magneticOperator p.b coupling p.potential) s.vector‖ *
        ‖(q.correction : orthogonalComplement (s.vector : L2Space))‖ := by
    rw [heq]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hdiagonal := (abs_le.mp s.diagonal_error_le).1
  have hcoupling := mul_le_mul_of_nonneg_right s.coupling_le
    (norm_nonneg (q.correction : orthogonalComplement (s.vector : L2Space)))
  have hE : E ≤ atomicGroundEnergy p.b p.core coupling :=
    (sub_nonneg.mp q.energy_shift_bounds.1).trans s.diagonal_le
  rw [abs_of_nonpos (sub_nonpos.mpr hE)]
  nlinarith only [hinner, hdiagonal, hcoupling]

/-- At the already constructed normalization threshold the coefficient is
uniform, and the force still appears only once. -/
theorem energy_shift_le_three_forcing
    (hc : (1 / 2 : ℝ) ≤
      schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))) :
    |E - atomicGroundEnergy p.b p.core coupling| ≤
      3 * ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp
        (s.vector : L2Space)‖ := by
  have hsq := norm_sq_le_three_of_half_le_schurNormalization hc
  have hn : ‖(q.correction : orthogonalComplement (s.vector : L2Space))‖ ≤ 2 := by
    nlinarith [norm_nonneg (q.correction : orthogonalComplement (s.vector : L2Space))]
  exact (s.energy_shift_le_forcing q).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- In the semi-classical convention the factor `λ²` cancels exactly. -/
theorem scaled_energy_shift_le_three_forcing (hcoupling : 0 < coupling)
    (hc : (1 / 2 : ℝ) ≤
      schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space))) :
    |(coupling⁻¹) ^ 2 * (E - atomicGroundEnergy p.b p.core coupling)| ≤
      3 * ‖CuspParameters.atomicPerturbationMul hp (s.vector : L2Space)‖ := by
  have hbound := s.energy_shift_le_three_forcing q hc
  have hforce : ‖(coupling ^ 2 : ℂ) • CuspParameters.atomicPerturbationMul hp
      (s.vector : L2Space)‖ =
      coupling ^ 2 * ‖CuspParameters.atomicPerturbationMul hp (s.vector : L2Space)‖ := by
    rw [norm_smul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg coupling)]
  rw [hforce] at hbound
  have hcancel : (coupling⁻¹) ^ 2 * coupling ^ 2 = 1 := by field_simp
  calc
    _ = (coupling⁻¹) ^ 2 * |E - atomicGroundEnergy p.b p.core coupling| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ (coupling⁻¹) ^ 2 * (3 * (coupling ^ 2 *
        ‖CuspParameters.atomicPerturbationMul hp (s.vector : L2Space)‖)) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = ((coupling⁻¹) ^ 2 * coupling ^ 2) *
        (3 * ‖CuspParameters.atomicPerturbationMul hp (s.vector : L2Space)‖) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- A nonnegative exponential weight can only enlarge the one forcing norm.
No preservation of the operator domain by the weight is used. -/
theorem scaled_energy_shift_le_three_weighted_forcing (hcoupling : 0 < coupling)
    (hc : (1 / 2 : ℝ) ≤
      schurNormalization (q.correction : orthogonalComplement (s.vector : L2Space)))
    (T : Plane → ℝ) (hTc : Continuous T) {M κ : ℝ}
    (hT : ∀ x, T x ∈ Icc 0 M) (hκ : 0 ≤ κ) :
    |(coupling⁻¹) ^ 2 * (E - atomicGroundEnergy p.b p.core coupling)| ≤
      3 * ‖atomicExponentialWeightMul T hTc hT coupling κ
        (CuspParameters.atomicPerturbationMul hp (s.vector : L2Space))‖ := by
  exact (s.scaled_energy_shift_le_three_forcing q hcoupling hc).trans
    (mul_le_mul_of_nonneg_left
      (norm_le_atomicExponentialWeightMul T hTc hT hcoupling.le hκ _) (by norm_num))

end AtomicSchurReference
end InfiniteZero
