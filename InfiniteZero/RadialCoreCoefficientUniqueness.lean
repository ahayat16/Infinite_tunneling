import InfiniteZero.RadialCoreGroundChoice
import InfiniteZero.RadialCoreExteriorState

/-!
# Uniqueness of the positive radial reference and its tail coefficient

Simplicity determines a normalized ground state up to a unit phase.
Pointwise real positivity fixes that phase exactly. The exterior coefficient
is then unique for the very same state; positivity of the state already
rules out a zero kernel value, without an additional energy hypothesis.
-/

noncomputable section

namespace InfiniteZero

/-- Real positivity removes the unit-phase ambiguity, already at the origin. -/
theorem IsPositiveRadial.eq_of_unit_smul {φ ψ : Wavefunction}
    (hφ : IsPositiveRadial φ) (hψ : IsPositiveRadial ψ)
    {z : ℂ} (hz : ‖z‖ = 1) (hphase : ψ = z • φ) : φ = ψ := by
  have hφim : (φ 0).im = 0 := by rw [hφ.radial 0]; rfl
  have hψim : (ψ 0).im = 0 := by rw [hψ.radial 0]; rfl
  have hφre := hφ.positive 0
  have hψre := hψ.positive 0
  have hzero := congrFun hphase 0
  simp only [Pi.smul_apply, smul_eq_mul] at hzero
  have him := congrArg Complex.im hzero
  simp only [hψim, Complex.mul_im, hφim, mul_zero, zero_add] at him
  have hzim : z.im = 0 := by nlinarith
  have hre := congrArg Complex.re hzero
  simp only [Complex.mul_re, hφim, mul_zero, sub_zero] at hre
  have hzre : 0 < z.re := by
    by_contra hn
    have hznonpos : z.re ≤ 0 := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg hznonpos hφre.le
    linarith
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hzim
  have hzabs : |z.re| = 1 := by
    have hn := hz
    rw [hzreal, Complex.norm_real, Real.norm_eq_abs] at hn
    exact hn
  have hzreone : z.re = 1 := by simpa only [abs_of_pos hzre] using hzabs
  have hzone : z = 1 := by rw [hzreal, hzreone, Complex.ofReal_one]
  simpa only [hzone, one_smul] using hphase.symm

/-- Simplicity plus positive radial representatives gives pointwise equality. -/
theorem AtomicGroundSimple.eq_of_positiveRadial
    {b coupling : ℝ} {V : Potential} (hsimple : AtomicGroundSimple b V coupling)
    {φ ψ : Wavefunction} (hφ : IsAtomicGroundState b V coupling φ)
    (hφpos : IsPositiveRadial φ) (hψ : IsAtomicGroundState b V coupling ψ)
    (hψpos : IsPositiveRadial ψ) : φ = ψ := by
  obtain ⟨z, hz, hphase⟩ := hsimple φ ψ hφ hψ
  exact hφpos.eq_of_unit_smul hψpos hz hphase

/-- Two coefficients representing the exterior tail of the same positive
state coincide. No independent positivity assumption on the kernel or the
coefficients is needed. -/
theorem IsPositiveRadial.landau_coefficient_unique
    {φ : Wavefunction} (hφ : IsPositiveRadial φ)
    {b h E r₀ Γ₁ Γ₂ : ℝ}
    (htail₁ : ∀ x : Plane, r₀ < ‖x‖ → φ x = (Γ₁ * landauKernel b h E ‖x‖ : ℂ))
    (htail₂ : ∀ x : Plane, r₀ < ‖x‖ → φ x = (Γ₂ * landauKernel b h E ‖x‖ : ℂ)) :
    Γ₁ = Γ₂ := by
  let x : Plane := (|r₀| + 1) • coordinateVector 0
  have hxnorm : ‖x‖ = |r₀| + 1 := norm_radial_axis (by positivity)
  have hx : r₀ < ‖x‖ := by rw [hxnorm]; linarith [le_abs_self r₀]
  have hK : landauKernel b h E ‖x‖ ≠ 0 := by
    intro hzero
    have hv : φ x = 0 := by simpa only [hzero, Complex.ofReal_zero, mul_zero] using htail₁ x hx
    have hp := hφ.positive x
    rw [hv, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  have heq := congrArg Complex.re ((htail₁ x hx).symm.trans (htail₂ x hx))
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at heq
  exact mul_right_cancel₀ hK heq

namespace RadialCoreSpectralData

/-- Every normalized positive radial core ground state is the same function
once the original radial gap is available. -/
theorem positive_ground_unique {b : ℝ} {p : CuspParameters}
    (hRad : RadialCoreSpectralData b p) (hr : 0 < p.r₀) {coupling : ℝ}
    (hAcore : IsMagneticRealization b coupling p.core) (hT : hRad.threshold ≤ coupling)
    {φ ψ : Wavefunction} (hφ : IsAtomicGroundState b p.core coupling φ)
    (hφpos : IsPositiveRadial φ) (hψ : IsAtomicGroundState b p.core coupling ψ)
    (hψpos : IsPositiveRadial ψ) : φ = ψ :=
  (hRad.core_groundSimple hr hAcore hT).eq_of_positiveRadial hφ hφpos hψ hψpos

/-- Universal alignment of two supplied true states and their own exact
exterior coefficients. Neither state nor coefficient is selected anew. -/
theorem positive_ground_coefficient_unique {b : ℝ} {p : CuspParameters}
    (hRad : RadialCoreSpectralData b p) (hr : 0 < p.r₀) {coupling : ℝ}
    (hAcore : IsMagneticRealization b coupling p.core) (hT : hRad.threshold ≤ coupling)
    {φ ψ : Wavefunction} (hφ : IsAtomicGroundState b p.core coupling φ)
    (hφpos : IsPositiveRadial φ) (hψ : IsAtomicGroundState b p.core coupling ψ)
    (hψpos : IsPositiveRadial ψ) {Γ₁ Γ₂ : ℝ}
    (htail₁ : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ₁ * landauKernel b coupling⁻¹
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ))
    (htail₂ : ∀ x : Plane, p.r₀ < ‖x‖ →
      ψ x = (Γ₂ * landauKernel b coupling⁻¹
        (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ)) :
    φ = ψ ∧ Γ₁ = Γ₂ := by
  have hstate := hRad.positive_ground_unique hr hAcore hT hφ hφpos hψ hψpos
  refine ⟨hstate, hφpos.landau_coefficient_unique htail₁ ?_⟩
  simpa only [hstate] using htail₂

end RadialCoreSpectralData
end InfiniteZero
