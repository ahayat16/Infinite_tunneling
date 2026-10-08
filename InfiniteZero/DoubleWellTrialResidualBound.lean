import InfiniteZero.DoubleWellTrialDomain
import InfiniteZero.LocalizedOverlap
import InfiniteZero.SeparationCertificate

/-!
# Opposite-well residuals controlled by the actual exterior mass

Separation puts the support of the opposite potential in the exterior tail
of each translated atom. The exact domain identities then give a bound for
the genuine operator residual, without any sign assumption on its energy.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

theorem norm_boundedPotentialMul_sq_le_setIntegral
    (W : Potential) (hW : Continuous W) (hbound : ∀ x, |W x| ≤ 1)
    {S : Set Plane} (hS : MeasurableSet S) (hzero : ∀ x, x ∉ S → W x = 0)
    {u : L2Space} {ψ : Wavefunction} (hu : Represents u ψ) :
    ‖boundedPotentialMul W hW hbound u‖ ^ 2 ≤ ∫ x in S, ‖ψ x‖ ^ 2 := by
  have hrep : Represents (boundedPotentialMul W hW hbound u)
      (fun x => (W x : ℂ) * ψ x) := by
    filter_upwards [coe_boundedPotentialMul W hW hbound u, hu] with x hx hux
    simpa only [hux] using hx
  rw [hrep.norm_sq_eq_mass, mass, ← integral_indicator hS]
  apply integral_mono hrep.memLp.norm.integrable_sq
    (hu.memLp.norm.integrable_sq.indicator hS)
  intro x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    dsimp only
    rw [norm_mul, mul_pow]
    have hb : ‖(W x : ℂ)‖ ^ 2 ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, one_pow] using
        pow_le_pow_left₀ (abs_nonneg (W x)) (hbound x) 2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (sq_nonneg ‖ψ x‖)
  · simp only [indicator_of_notMem hx, hzero x hx, Complex.ofReal_zero,
      zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0), le_refl]

namespace CuspParameters

theorem opposite_potential_zero_of_left_near {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) {x : Plane}
    (hx : ‖x + displacement L‖ < 4 * p.r₀) :
    p.potential (-x + displacement L) = 0 := by
  by_contra hn
  have hsupport := cert.support_bound _ (subset_tsupport _ hn)
  have hR : p.R < L := ((le_max_right _ _).trans_lt cert.separation).trans_le hL
  have ha : cert.supportRadius < L :=
    ((le_max_left _ _).trans_lt cert.separation).trans_le hL
  have hLp : 0 < L := hp.radius_pos.trans hR
  have hd : ‖displacement L + displacement L‖ = 2 * L := by
    rw [← two_smul ℝ, norm_smul]
    simp [displacement, coordinateVector, norm_smul, Real.norm_eq_abs, abs_of_pos hLp]
  have htriangle := norm_add_le (x + displacement L) (-x + displacement L)
  rw [show x + displacement L + (-x + displacement L) =
    displacement L + displacement L by abel, hd] at htriangle
  linarith [hp.radius_large, hp.r₀_pos]

theorem opposite_potential_zero_of_right_near {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) {x : Plane}
    (hx : ‖displacement L - x‖ < 4 * p.r₀) :
    p.potential (x + displacement L) = 0 := by
  have h := opposite_potential_zero_of_left_near hp cert hL
    (x := -x) (by simpa only [neg_add_eq_sub] using hx)
  simpa only [neg_neg] using h

theorem norm_oppositePotentialMul_left_sq_le_tail {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L coupling : ℝ} (hL : cert.L₀ ≤ L)
    {u : L2Space} {φ : Wavefunction} (hu : Represents u (leftState p.b L coupling φ)) :
    let W : Potential := fun x => p.potential (-x + displacement L)
    let hW : Continuous W := (potential_contDiff hp).continuous.comp
      (continuous_neg.add continuous_const)
    let hbound : ∀ x, |W x| ≤ 1 := fun x => abs_le.mpr
      ⟨(potential_range hp _).1, (potential_range hp _).2.trans (by norm_num)⟩
    ‖boundedPotentialMul W hW hbound u‖ ^ 2 ≤
      ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  dsimp only
  rw [← setIntegral_leftState_tail p.b L coupling (4 * p.r₀) φ]
  apply norm_boundedPotentialMul_sq_le_setIntegral _ _ _
    ((isClosed_le continuous_const (continuous_id.add continuous_const).norm).measurableSet)
    (fun x hx => opposite_potential_zero_of_left_near hp cert hL (lt_of_not_ge hx)) hu

theorem norm_oppositePotentialMul_right_sq_le_tail {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L coupling : ℝ} (hL : cert.L₀ ≤ L)
    {u : L2Space} {φ : Wavefunction} (hu : Represents u (rightState p.b L coupling φ)) :
    let W : Potential := fun x => p.potential (x + displacement L)
    let hW : Continuous W := (potential_contDiff hp).continuous.comp
      (continuous_id.add continuous_const)
    let hbound : ∀ x, |W x| ≤ 1 := fun x => abs_le.mpr
      ⟨(potential_range hp _).1, (potential_range hp _).2.trans (by norm_num)⟩
    ‖boundedPotentialMul W hW hbound u‖ ^ 2 ≤
      ∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2 := by
  dsimp only
  rw [← setIntegral_rightState_tail p.b L coupling (4 * p.r₀) φ]
  apply norm_boundedPotentialMul_sq_le_setIntegral _ _ _
    ((isClosed_le continuous_const (continuous_const.sub continuous_id).norm).measurableSet)
    (fun x hx => opposite_potential_zero_of_right_near hp cert hL (lt_of_not_ge hx)) hu

/-- This scalar conversion keeps the `λ exp(-dλ)` factor of the true residual. -/
theorem norm_scaled_vector_le_of_tail_bound
    {coupling C d tail : ℝ} (hc : 0 < coupling) (hC : 0 ≤ C)
    {u : L2Space} (hu : ‖u‖ ^ 2 ≤ tail)
    (htail : tail ≤ (C / coupling ^ 2) * Real.exp (-2 * d * coupling)) :
    ‖(coupling ^ 2 : ℂ) • u‖ ≤ Real.sqrt C * coupling * Real.exp (-d * coupling) := by
  have hexp : Real.exp (-2 * d * coupling) = Real.exp (-d * coupling) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquare := mul_le_mul_of_nonneg_left (hu.trans htail)
    (sq_nonneg (coupling ^ 2))
  have hleft : ‖(coupling ^ 2 : ℂ) • u‖ ^ 2 = (coupling ^ 2) ^ 2 * ‖u‖ ^ 2 := by
    simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have hright : (coupling ^ 2) ^ 2 *
      ((C / coupling ^ 2) * Real.exp (-2 * d * coupling)) =
        (Real.sqrt C * coupling * Real.exp (-d * coupling)) ^ 2 := by
    rw [hexp]
    simp only [mul_pow, Real.sq_sqrt hC]
    field_simp
  rw [← hleft, hright] at hsquare
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hc.le) (Real.exp_pos _).le)).mp hsquare

theorem exists_leftState_double_operator_vector_residual_le {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {coupling L C d : ℝ} (hc : 0 < coupling) (hL : cert.L₀ ≤ L) (hC : 0 ≤ C)
    {φ : Wavefunction} (hφ : IsAtomicGroundState p.b p.potential coupling φ)
    (htail : (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
      (C / coupling ^ 2) * Real.exp (-2 * d * coupling))
    (hAleft : IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAdouble : IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
      Represents (u : L2Space) (leftState p.b L coupling φ) ∧ ‖(u : L2Space)‖ = 1 ∧
      ‖magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
          (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space)‖ ≤
        Real.sqrt C * coupling * Real.exp (-d * coupling) := by
  have hbound : ∀ x, |p.potential x| ≤ 1 := fun x => abs_le.mpr
    ⟨(potential_range hp x).1, (potential_range hp x).2.trans (by norm_num)⟩
  obtain ⟨u, hu, hn, he⟩ := hφ.exists_leftState_double_operator_vector
    (potential_contDiff hp).continuous hbound hAleft hAdouble
  refine ⟨u, hu, hn, ?_⟩
  rw [he, add_sub_cancel_left]
  exact norm_scaled_vector_le_of_tail_bound hc hC
    (norm_oppositePotentialMul_left_sq_le_tail hp cert hL hu) htail

theorem exists_rightState_double_operator_vector_residual_le {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {coupling L C d : ℝ} (hc : 0 < coupling) (hL : cert.L₀ ≤ L) (hC : 0 ≤ C)
    {φ : Wavefunction} (hφ : IsAtomicGroundState p.b p.potential coupling φ)
    (htail : (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
      (C / coupling ^ 2) * Real.exp (-2 * d * coupling))
    (hAright : IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : IsMagneticRealization p.b coupling (doubleWellPotential p.potential L)) :
    ∃ u : (magneticOperator p.b coupling (doubleWellPotential p.potential L)).domain,
      Represents (u : L2Space) (rightState p.b L coupling φ) ∧ ‖(u : L2Space)‖ = 1 ∧
      ‖magneticOperator p.b coupling (doubleWellPotential p.potential L) u -
          (atomicGroundEnergy p.b p.potential coupling : ℂ) • (u : L2Space)‖ ≤
        Real.sqrt C * coupling * Real.exp (-d * coupling) := by
  have hbound : ∀ x, |p.potential x| ≤ 1 := fun x => abs_le.mpr
    ⟨(potential_range hp x).1, (potential_range hp x).2.trans (by norm_num)⟩
  obtain ⟨u, hu, hn, he⟩ := hφ.exists_rightState_double_operator_vector
    (potential_contDiff hp).continuous hbound hAright hAdouble
  refine ⟨u, hu, hn, ?_⟩
  rw [he, add_sub_cancel_left]
  exact norm_scaled_vector_le_of_tail_bound hc hC
    (norm_oppositePotentialMul_right_sq_le_tail hp cert hL hu) htail

end CuspParameters
end InfiniteZero
