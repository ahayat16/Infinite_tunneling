import InfiniteZero.ParityTrialRayleigh
import InfiniteZero.ParityTrialEnergyBound

/-!
# Exact physical masses of translated-state residuals

The actual double-well operator residual equals multiplication by the
opposite potential. Its squared norm is therefore the physical mass of
that product times the fourth power of the coupling. Inversion identifies
the left and right masses, and normalization of a parity trial costs at
most a factor four in the squared residual when the overlap is at most one half.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem Represents.norm_boundedPotentialMul_sq_eq_mass
    {u : L2Space} {ψ : Wavefunction} (hu : Represents u ψ)
    (W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    ‖boundedPotentialMul W hW hbound u‖ ^ 2 =
      mass (fun x => (W x : ℂ) * ψ x) := by
  apply Represents.norm_sq_eq_mass
  filter_upwards [coe_boundedPotentialMul W hW hbound u, hu] with x hx hux
  simpa only [hux] using hx

theorem Represents.norm_scaled_boundedPotentialMul_sq_eq_mass
    {u : L2Space} {ψ : Wavefunction} (hu : Represents u ψ)
    (W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C)
    (coupling : ℝ) :
    ‖(coupling ^ 2 : ℂ) • boundedPotentialMul W hW hbound u‖ ^ 2 =
      coupling ^ 4 * mass (fun x => (W x : ℂ) * ψ x) := by
  rw [norm_smul, mul_pow, hu.norm_boundedPotentialMul_sq_eq_mass]
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [← pow_mul, show 2 * 2 = 4 from rfl, pow_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ coupling ^ 4)]

/-- Inversion exchanges the two opposite-potential products exactly. -/
theorem mass_oppositePotential_left_eq_right (b L coupling : ℝ)
    (v : Potential) (φ : Wavefunction) :
    mass (fun x => (v (-x + displacement L) : ℂ) * leftState b L coupling φ x) =
      mass (fun x => (v (x + displacement L) : ℂ) * rightState b L coupling φ x) := by
  simpa only [rightState, neg_neg] using
    mass_inversion (fun x => (v (x + displacement L) : ℂ) * rightState b L coupling φ x)

theorem IsAtomicGroundState.leftState_residual_sq_eq_mass
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : Represents (u : L2Space) (leftState b L coupling φ)) :
    ‖magneticOperator b coupling (doubleWellPotential v L) u -
        (atomicGroundEnergy b v coupling : ℂ) • (u : L2Space)‖ ^ 2 =
      coupling ^ 4 *
        mass (fun x => (v (-x + displacement L) : ℂ) * leftState b L coupling φ x) := by
  obtain ⟨l, hl, _, hAl⟩ := hφ.exists_leftState_double_operator_vector
    hv hbound hAleft hAdouble
  have hul : u = l := Subtype.ext (Lp.ext (hu.trans hl.symm))
  subst u
  rw [hAl, add_sub_cancel_left]
  exact hl.norm_scaled_boundedPotentialMul_sq_eq_mass _ _ _ coupling

theorem IsAtomicGroundState.rightState_residual_sq_eq_mass
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : Represents (u : L2Space) (rightState b L coupling φ)) :
    ‖magneticOperator b coupling (doubleWellPotential v L) u -
        (atomicGroundEnergy b v coupling : ℂ) • (u : L2Space)‖ ^ 2 =
      coupling ^ 4 *
        mass (fun x => (v (x + displacement L) : ℂ) * rightState b L coupling φ x) := by
  obtain ⟨r, hr, _, hAr⟩ := hφ.exists_rightState_double_operator_vector
    hv hbound hAright hAdouble
  have hur : u = r := Subtype.ext (Lp.ext (hu.trans hr.symm))
  subst u
  rw [hAr, add_sub_cancel_left]
  exact hr.norm_scaled_boundedPotentialMul_sq_eq_mass _ _ _ coupling

private theorem norm_normalized_signedSum_residual_le
    (A : L2Space →ₗ.[ℂ] L2Space) (E R : ℝ) (l r : A.domain)
    (hl : ‖A l - (E : ℂ) • (l : L2Space)‖ ≤ R)
    (hr : ‖A r - (E : ℂ) • (r : L2Space)‖ ≤ R)
    (even : Bool) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖A (c • (if even then l + r else l - r)) -
      (E : ℂ) • ((c • (if even then l + r else l - r) : A.domain) : L2Space)‖
      ≤ 2 * R := by
  let raw : A.domain := if even then l + r else l - r
  have hraw : ‖A raw - (E : ℂ) • (raw : L2Space)‖ ≤ 2 * R := by
    cases even
    · change ‖A (l - r) - (E : ℂ) • ((l - r : A.domain) : L2Space)‖ ≤ _
      simp only [LinearPMap.map_sub, Submodule.coe_sub, smul_sub]
      rw [show A l - A r - ((E : ℂ) • (l : L2Space) - (E : ℂ) • (r : L2Space)) =
        (A l - (E : ℂ) • (l : L2Space)) - (A r - (E : ℂ) • (r : L2Space)) by abel]
      exact (norm_sub_le _ _).trans (by linarith)
    · change ‖A (l + r) - (E : ℂ) • ((l + r : A.domain) : L2Space)‖ ≤ _
      simp only [LinearPMap.map_add, Submodule.coe_add, smul_add]
      rw [show A l + A r - ((E : ℂ) • (l : L2Space) + (E : ℂ) • (r : L2Space)) =
        (A l - (E : ℂ) • (l : L2Space)) + (A r - (E : ℂ) • (r : L2Space)) by abel]
      exact (norm_add_le _ _).trans (by linarith)
  change ‖A (c • raw) - (E : ℂ) • ((c • raw : A.domain) : L2Space)‖ ≤ _
  rw [LinearPMap.map_smul, Submodule.coe_smul, smul_comm (E : ℂ) c, ← smul_sub, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans hraw

/-- Every genuine representative of the normalized parity trial satisfies
the physical opposite-well mass bound. No small residual is assumed. -/
theorem IsAtomicGroundState.normalizedParityTrial_residual_sq_le_mass
    {b coupling L : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hv : Continuous v)
    {C : ℝ} (hbound : ∀ x, |v x| ≤ C)
    (hAleft : IsMagneticRealization b coupling (fun x => v (x + displacement L)))
    (hAright : IsMagneticRealization b coupling (fun x => v (displacement L - x)))
    (hAdouble : IsMagneticRealization b coupling (doubleWellPotential v L))
    (even : Bool) (hs : |translatedOverlap b L coupling φ| ≤ 1 / 2)
    (u : (magneticOperator b coupling (doubleWellPotential v L)).domain)
    (hu : Represents (u : L2Space) (normalizedParityTrialState even b L coupling φ)) :
    ‖magneticOperator b coupling (doubleWellPotential v L) u -
        (atomicGroundEnergy b v coupling : ℂ) • (u : L2Space)‖ ^ 2 ≤
      4 * coupling ^ 4 *
        mass (fun x => (v (x + displacement L) : ℂ) * rightState b L coupling φ x) := by
  let A := magneticOperator b coupling (doubleWellPotential v L)
  let E := atomicGroundEnergy b v coupling
  obtain ⟨l, hl, _, _⟩ := hφ.exists_leftState_double_operator_vector hv hbound hAleft hAdouble
  obtain ⟨r, hr, _, _⟩ := hφ.exists_rightState_double_operator_vector hv hbound hAright hAdouble
  have hlmass := hφ.leftState_residual_sq_eq_mass hv hbound hAleft hAdouble l hl
  rw [mass_oppositePotential_left_eq_right] at hlmass
  have hrmass := hφ.rightState_residual_sq_eq_mass hv hbound hAright hAdouble r hr
  have hlr : ‖A l - (E : ℂ) • (l : L2Space)‖ ≤
      ‖A r - (E : ℂ) • (r : L2Space)‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hlmass.trans hrmass.symm).le
  let c : ℂ := ((Real.sqrt (parityTrialMass even b L coupling φ))⁻¹ : ℂ)
  let q : A.domain := c • (if even then l + r else l - r)
  have hrJ : (r : L2Space) = l2Inversion (l : L2Space) :=
    Lp.ext (hr.trans hl.inversion.symm)
  have hq : Represents (q : L2Space) (normalizedParityTrialState even b L coupling φ) := by
    have h := hl.normalizedParityTrialState even
    rw [← hrJ] at h
    cases even <;> simpa only [q, c, Bool.false_eq_true, ↓reduceIte,
      Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub] using h
  have huq : u = q := Subtype.ext (Lp.ext (hu.trans hq.symm))
  have hres := norm_normalized_signedSum_residual_le A E
    ‖A r - (E : ℂ) • (r : L2Space)‖ l r hlr le_rfl even c
      (norm_parityTrial_normalization_le_one even hs)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hres 2
  rw [huq]
  calc
    ‖A q - (E : ℂ) • (q : L2Space)‖ ^ 2 ≤
        (2 * ‖A r - (E : ℂ) • (r : L2Space)‖) ^ 2 := hsq
    _ = 4 * coupling ^ 4 *
        mass (fun x => (v (x + displacement L) : ℂ) * rightState b L coupling φ x) := by
      rw [mul_pow, hrmass]
      ring

end InfiniteZero
