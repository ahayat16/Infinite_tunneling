import InfiniteZero.ParityTrialDomain
import InfiniteZero.ParityTrialL2
import InfiniteZero.AtomicPerturbationSign
import InfiniteZero.SchurEigenvector
import InfiniteZero.ParityTransfer

/-!
# Exact physical Rayleigh quotients of the normalized parity trials

All vectors belong to the actual double-well domain. The coefficients
are the genuine overlap, diagonal potential integral, and hopping.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

/-- The diagonal defect for an arbitrary atomic ground-state representative. -/
def translatedDefect (b : ℝ) (v : Potential) (L coupling : ℝ) (φ : Wavefunction) : ℝ :=
  coupling ^ 2 * ∫ x : Plane, v (-x + displacement L) * ‖leftState b L coupling φ x‖ ^ 2

theorem translatedDefect_eq_right (b : ℝ) (v : Potential) (L coupling : ℝ)
    (φ : Wavefunction) :
    translatedDefect b v L coupling φ =
      coupling ^ 2 * ∫ x : Plane, v (x + displacement L) * ‖rightState b L coupling φ x‖ ^ 2 := by
  unfold translatedDefect
  congr 1
  simpa only [rightState, neg_neg] using
    (integral_neg_eq_self
      (fun x : Plane => v (x + displacement L) * ‖rightState b L coupling φ x‖ ^ 2) volume)

theorem Represents.re_inner_boundedPotentialMul_eq_integral
    {u : L2Space} {ψ : Wavefunction} (hu : Represents u ψ)
    (W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    (inner ℂ u (boundedPotentialMul W hW hbound u)).re =
      ∫ x : Plane, W x * ‖ψ x‖ ^ 2 := by
  rw [InfiniteZero.re_inner_boundedPotentialMul_eq_integral]
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hx]

theorem inner_boundedPotentialMul_eq_waveInner
    {u w : L2Space} {ψ χ : Wavefunction} (hu : Represents u ψ) (hw : Represents w χ)
    (W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    inner ℂ u (boundedPotentialMul W hW hbound w) =
      waveInner ψ (fun x => (W x : ℂ) * χ x) := by
  apply hu.inner_eq_waveInner
  filter_upwards [coe_boundedPotentialMul W hW hbound w, hw] with x hx hwx
  rw [hx, hwx]

theorem hopping_eq_inner_boundedPotentialMul
    {b L coupling : ℝ} {v : Potential} {φ : Wavefunction}
    {u w : L2Space} (hu : Represents u (leftState b L coupling φ))
    (hw : Represents w (rightState b L coupling φ))
    (hv : Continuous v) {C : ℝ} (hbound : ∀ x, |v x| ≤ C) :
    hopping b v L coupling φ = (coupling ^ 2 : ℂ) *
      inner ℂ u (boundedPotentialMul (fun x => v (x + displacement L))
        (hv.comp (continuous_id.add continuous_const))
        (fun x => hbound (x + displacement L)) w) := by
  rw [inner_boundedPotentialMul_eq_waveInner hu hw]
  simp only [hopping, waveInner, Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

section Algebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem schurDiagonal_real_smul (A : H →ₗ.[ℂ] H) (u : A.domain) (r : ℝ) :
    schurDiagonal A ((r : ℂ) • u) = r ^ 2 * schurDiagonal A u := by
  simp only [schurDiagonal, A.map_smul, Submodule.coe_smul, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem schurDiagonal_normalized_signedSum
    (A : H →ₗ.[ℂ] H) (l r : A.domain) (E δ ρ s : ℝ)
    (hl : schurDiagonal A l = E + δ) (hr : schurDiagonal A r = E + δ)
    (hlr : (inner ℂ (l : H) (A r)).re = E * s + ρ)
    (hrl : (inner ℂ (r : H) (A l)).re = E * s + ρ)
    (hs : |s| < 1) (even : Bool) :
    schurDiagonal A
      (((Real.sqrt (if even then 2 * (1 + s) else 2 * (1 - s)))⁻¹ : ℂ) •
        (if even then l + r else l - r)) =
      E + (δ + if even then ρ else -ρ) / (1 + if even then s else -s) := by
  have habs := abs_lt.mp hs
  cases even
  · have hd : 0 < 2 * (1 - s) := by linarith
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Complex.ofReal_inv, schurDiagonal_real_smul, inv_pow, Real.sq_sqrt hd.le]
    have hraw : schurDiagonal A (l - r) = 2 * (E + δ) - 2 * (E * s + ρ) := by
      simp only [schurDiagonal, A.map_sub, Submodule.coe_sub,
        inner_sub_left, inner_sub_right, Complex.sub_re]
      change schurDiagonal A l - (inner ℂ (r : H) (A l)).re -
        ((inner ℂ (l : H) (A r)).re - schurDiagonal A r) = _
      rw [hl, hr, hlr, hrl]
      ring
    rw [hraw]
    have hds : 1 - s ≠ 0 := by linarith
    simp only [← sub_eq_add_neg]
    field_simp [hds]
    ring
  · have hd : 0 < 2 * (1 + s) := by linarith
    simp only [↓reduceIte]
    rw [← Complex.ofReal_inv, schurDiagonal_real_smul, inv_pow, Real.sq_sqrt hd.le]
    have hraw : schurDiagonal A (l + r) = 2 * (E + δ) + 2 * (E * s + ρ) := by
      simp only [schurDiagonal, A.map_add, Submodule.coe_add,
        inner_add_left, inner_add_right, Complex.add_re]
      change schurDiagonal A l + (inner ℂ (r : H) (A l)).re +
        ((inner ℂ (l : H) (A r)).re + schurDiagonal A r) = _
      rw [hl, hr, hlr, hrl]
      ring
    rw [hraw]
    have hds : 1 + s ≠ 0 := by linarith
    field_simp [hds]
    ring
end Algebra

theorem schurDiagonal_of_boundedPotential_residual
    (A : L2Space →ₗ.[ℂ] L2Space) (u : A.domain) {ψ : Wavefunction}
    (hu : Represents (u : L2Space) ψ) (hn : ‖(u : L2Space)‖ = 1)
    (W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C)
    (E coupling : ℝ)
    (hAu : A u = (E : ℂ) • (u : L2Space) +
      (coupling ^ 2 : ℂ) • boundedPotentialMul W hW hbound (u : L2Space)) :
    schurDiagonal A u = E + coupling ^ 2 * ∫ x : Plane, W x * ‖ψ x‖ ^ 2 := by
  rw [schurDiagonal, hAu, inner_add_right, inner_smul_right, inner_smul_right,
    Complex.add_re]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hninner : (inner ℂ (u : L2Space) (u : L2Space)).re = ‖(u : L2Space)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (u : L2Space)).symm
  rw [hninner, hn, one_pow, mul_one, hu.re_inner_boundedPotentialMul_eq_integral]

theorem IsAtomicGroundState.schurDiagonal_normalizedParityTrialState
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) (hs : |translatedOverlap b L coupling φ| < 1)
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : Represents (u : L2Space) (normalizedParityTrialState even b L coupling φ)) :
    schurDiagonal (magneticOperator b coupling (doubleWellPotential v L)) u =
      atomicGroundEnergy b v coupling +
        (translatedDefect b v L coupling φ +
          if even then (hopping b v L coupling φ).re else -(hopping b v L coupling φ).re) /
        (1 + if even then translatedOverlap b L coupling φ else -translatedOverlap b L coupling φ) := by
  let A := magneticOperator b coupling (doubleWellPotential v L)
  let E := atomicGroundEnergy b v coupling
  obtain ⟨l, hl, hln, hAl⟩ := hφ.exists_leftState_double_operator_vector
    hv hbound hAleft hAdouble
  obtain ⟨r, hr, hrn, hAr⟩ := hφ.exists_rightState_double_operator_vector
    hv hbound hAright hAdouble
  have hdl : schurDiagonal A l = E + translatedDefect b v L coupling φ :=
    schurDiagonal_of_boundedPotential_residual A l hl hln
      (fun x => v (-x + displacement L)) (hv.comp (continuous_neg.add continuous_const))
      (fun x => hbound (-x + displacement L)) E coupling hAl
  have hdr : schurDiagonal A r = E + translatedDefect b v L coupling φ := by
    rw [translatedDefect_eq_right]
    exact schurDiagonal_of_boundedPotential_residual A r hr hrn
      (fun x => v (x + displacement L)) (hv.comp (continuous_id.add continuous_const))
      (fun x => hbound (x + displacement L)) E coupling hAr
  have hcross : inner ℂ (l : L2Space) (A r) =
      (E : ℂ) * (translatedOverlap b L coupling φ : ℂ) + hopping b v L coupling φ := by
    rw [hAr, inner_add_right, inner_smul_right, inner_smul_right,
      hl.inner_eq_waveInner hr, waveInner_left_right_eq_overlap,
      hopping_eq_inner_boundedPotentialMul hl hr hv hbound]
  have hlr : (inner ℂ (l : L2Space) (A r)).re =
      E * translatedOverlap b L coupling φ + (hopping b v L coupling φ).re := by
    rw [hcross]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hrl : (inner ℂ (r : L2Space) (A l)).re =
      E * translatedOverlap b L coupling φ + (hopping b v L coupling φ).re := by
    have hsym := selfAdjoint_inner_of_mem_graph hAdouble.selfAdjoint
      (A.mem_graph l) (A.mem_graph r)
    change inner ℂ (A l) (r : L2Space) = inner ℂ (l : L2Space) (A r) at hsym
    have hre : (inner ℂ (r : L2Space) (A l)).re =
        (inner ℂ (A l) (r : L2Space)).re := inner_re_symm (𝕜 := ℂ) (r : L2Space) (A l)
    rw [hre, hsym, hlr]
  let q : A.domain :=
    ((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ) •
      (if even then l + r else l - r)
  have hrJ : (r : L2Space) = l2Inversion (l : L2Space) :=
    Lp.ext (hr.trans hl.inversion.symm)
  have hq : Represents (q : L2Space) (normalizedParityTrialState even b L coupling φ) := by
    have h := hl.normalizedParityTrialState even
    rw [← hrJ] at h
    cases even <;> simpa only [q, Bool.false_eq_true, ↓reduceIte,
      Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub] using h
  have huq : u = q := Subtype.ext (Lp.ext (hu.trans hq.symm))
  rw [huq]
  exact schurDiagonal_normalized_signedSum A l r E (translatedDefect b v L coupling φ)
    (hopping b v L coupling φ).re (translatedOverlap b L coupling φ) hdl hdr hlr hrl hs even

theorem IsAtomicGroundState.exists_normalizedParityTrialState_rayleigh
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) (hs : |translatedOverlap b L coupling φ| < 1) :
    ∃ u : (magneticOperator b coupling (doubleWellPotential v L)).domain,
      Represents (u : L2Space) (normalizedParityTrialState even b L coupling φ) ∧
      ‖(u : L2Space)‖ = 1 ∧ HasL2Parity even (u : L2Space) ∧
      schurDiagonal (magneticOperator b coupling (doubleWellPotential v L)) u =
        atomicGroundEnergy b v coupling +
          (translatedDefect b v L coupling φ +
            if even then (hopping b v L coupling φ).re else -(hopping b v L coupling φ).re) /
          (1 + if even then translatedOverlap b L coupling φ else -translatedOverlap b L coupling φ) := by
  obtain ⟨u, hu, hn, hp⟩ := hφ.exists_normalizedParityTrialState_unit_operator_vector
    hv hbound hAleft hAright hAdouble even hs
  exact ⟨u, hu, hn, hp,
    hφ.schurDiagonal_normalizedParityTrialState hv hbound hAleft hAright hAdouble even hs u hu⟩

theorem canonicalParityTrial_schurDiagonal
    {b coupling L : ℝ} {v : Potential}
    (hExists : ∃ φ, IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) (hs : |canonicalOverlap b v L coupling| < 1)
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : Represents (u : L2Space)
      (normalizedParityTrialState even b L coupling (canonicalAtomicState b v coupling))) :
    schurDiagonal (magneticOperator b coupling (doubleWellPotential v L)) u =
      atomicGroundEnergy b v coupling +
        (canonicalDefect b v L coupling +
          if even then (canonicalHopping b v L coupling).re else -(canonicalHopping b v L coupling).re) /
        (1 + if even then canonicalOverlap b v L coupling else -canonicalOverlap b v L coupling) :=
  (canonicalAtomicState_spec b v coupling hExists).schurDiagonal_normalizedParityTrialState
    hv hbound hAleft hAright hAdouble even hs u hu

end InfiniteZero
