import InfiniteZero.CoreRadialMonotonicity
import InfiniteZero.RadialEigenfunctionEquation
import InfiniteZero.RadialGroundMonotonicity
import InfiniteZero.RadialProfileLower
import InfiniteZero.RadialCenterLower
import InfiniteZero.RadialPlaneL2
import InfiniteZero.RadialCoreSpectralData
import InfiniteZero.RadialCoreExteriorState
import InfiniteZero.AtomicExteriorGraph

/-! Monotonicity and a uniform positive inner bound for the actual radial
core ground state. All profile estimates follow from its concrete equation,
normalization and exterior mass; no harmonic profile convergence is assumed. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

def coreRadialODECoefficient (b coupling : ℝ) (p : CuspParameters) (r : ℝ) : ℝ :=
  coupling ^ 2 * (b ^ 2 * r ^ 2 / 4 + p.coreRadialProfile r) -
    atomicGroundEnergy b p.core coupling

theorem coreRadialODECoefficient_monotoneOn {p : CuspParameters} (hr : 0 < p.r₀)
    (b coupling : ℝ) : MonotoneOn (coreRadialODECoefficient b coupling p) (Ici 0) := by
  intro r hr' s hs hrs
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left
    (CuspParameters.effectiveCoreRadialProfile_monotoneOn hr b hr' hs hrs)
    (sq_nonneg coupling)) _

theorem coreRadialODECoefficient_lower {p : CuspParameters} {b coupling : ℝ}
    (hE : atomicGroundEnergy b p.core coupling ≤ 0) (r : ℝ) :
    -(coupling ^ 2) ≤ coreRadialODECoefficient b coupling p r := by
  have h := mul_le_mul_of_nonneg_left
    (CuspParameters.neg_one_le_effectiveCoreRadialProfile p b r) (sq_nonneg coupling)
  dsimp only [coreRadialODECoefficient]
  nlinarith only [h, hE]

theorem IsAtomicGroundState.hasDerivAt_core_radial_flux
    {b coupling : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) (hpos : IsPositiveRadial φ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => s * deriv (realRadialProfile φ) s)
      (r * coreRadialODECoefficient b coupling p r * realRadialProfile φ r) r := by
  convert hφ.1.hasDerivAt_radial_flux hpos hr using 1
  dsimp only [coreRadialODECoefficient, CuspParameters.coreRadialProfile]
  ring

/-- The actual positive radial core state decreases on the whole half-line. -/
theorem IsAtomicGroundState.core_profile_antitone
    {b coupling : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hr : 0 < p.r₀) (hφ : IsAtomicGroundState b p.core coupling φ)
    (hpos : IsPositiveRadial φ) : AntitoneOn (realRadialProfile φ) (Ici 0) := by
  apply antitoneOn_of_radial_flux (realRadialProfile_contDiff hφ.1.1)
    (fun r _ => hpos.profile_pos r) (coreRadialODECoefficient_monotoneOn hr b coupling)
    (fun _ hr' => hφ.hasDerivAt_core_radial_flux hpos hr')
  apply integrableOn_radial_sq_of_memLp
  have hmem : MemLp φ 2 volume := hφ.1.2.1
  exact (memLp_congr_ae (Filter.Eventually.of_forall hpos.radial)).mp hmem

theorem IsAtomicGroundState.core_profile_quadratic_lower
    {b coupling : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hr : 0 < p.r₀) (hφ : IsAtomicGroundState b p.core coupling φ)
    (hpos : IsPositiveRadial φ) (hE : atomicGroundEnergy b p.core coupling ≤ 0)
    {r : ℝ} (hr' : 0 ≤ r) :
    realRadialProfile φ 0 * (1 - coupling ^ 2 * r ^ 2 / 4) ≤ realRadialProfile φ r := by
  have hm := hφ.core_profile_antitone hr hpos
  exact radial_profile_lower_of_flux_equation (realRadialProfile_contDiff hφ.1.1)
    (sq_nonneg coupling) (fun s _ => (hpos.profile_pos s).le)
    (fun s hs => hm (by simp) hs.le hs.le)
    (fun s _ => coreRadialODECoefficient_lower hE s)
    (fun _ hs => hφ.hasDerivAt_core_radial_flux hpos hs) hr'

/-- A fixed positive lower bound on the shrinking interval [0,1/coupling],
for every positive radial normalized core ground state. The constants
precede the coupling and the state. -/
theorem CuspParameters.exists_core_profile_lower_of_radialData
    {p : CuspParameters} {b : ℝ} (hr : 0 < p.r₀) (hRad : RadialCoreSpectralData b p)
    (hAcore : ∀ coupling, IsMagneticRealization b coupling p.core) :
    ∃ c > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ → IsPositiveRadial φ →
        ∀ r ∈ Icc 0 coupling⁻¹, c ≤ realRadialProfile φ r := by
  let c₀ := Real.sqrt (1 / (2 * Real.pi * p.r₀ ^ 2))
  have hc₀ : 0 < c₀ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨3 / 4 * c₀, mul_pos (by norm_num) hc₀,
    max hRad.threshold (2 * hRad.energyBound),
    hRad.threshold_pos.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc φ hφ hpos r hrange
  have hT := (le_max_left hRad.threshold (2 * hRad.energyBound)).trans hc
  have hB := (le_max_right hRad.threshold (2 * hRad.energyBound)).trans hc
  have hcpos : 0 < coupling := hRad.threshold_pos.trans_le hT
  obtain ⟨ψ, hψ, hupper, _⟩ := hRad.ground coupling hT
  have hquot : hRad.energyBound / coupling ≤ 1 / 2 :=
    (div_le_iff₀ hcpos).mpr (by linarith)
  have htail := (CuspParameters.core_exteriorMass_le_of_atomicGroundState hr hcpos
    (hAcore coupling) hφ hupper).trans hquot
  have hcenter : c₀ ≤ realRadialProfile φ 0 :=
    realRadialProfile_zero_lower_of_exteriorMass hr hφ.1.2.1 hφ.2 hpos
      (hφ.core_profile_antitone hr hpos) htail
  have hE : atomicGroundEnergy b p.core coupling < 0 := by
    by_contra he
    exact (not_lt_of_ge (mul_nonneg (sq_nonneg (coupling⁻¹)) (le_of_not_gt he)))
      (hRad.scaled_energy_neg hT hB)
  have hlow := hφ.core_profile_quadratic_lower hr hpos hE.le hrange.1
  have hmul : coupling * r ≤ 1 := by
    simpa only [mul_inv_cancel₀ hcpos.ne'] using
      mul_le_mul_of_nonneg_left hrange.2 hcpos.le
  have hsq : (coupling * r) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hcpos.le hrange.1) zero_le_one).mpr hmul
  have hprod := mul_le_mul_of_nonneg_left hsq (hpos.profile_pos 0).le
  nlinarith only [hlow, hprod, hcenter]

/-- The lower bound and the exterior coefficient refer to the same actual
normalized positive radial state. -/
theorem CuspParameters.exists_radialCore_kernel_profile_lower_of_radialData
    {p : CuspParameters} {b : ℝ} (hb : 0 < b) (hr : 0 < p.r₀)
    (hRad : RadialCoreSpectralData b p)
    (hAcore : ∀ coupling, IsMagneticRealization b coupling p.core) :
    ∃ c > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ ∧
        (∀ r ∈ Icc 0 coupling⁻¹, c ≤ realRadialProfile φ r) ∧
        ∃ Γ : ℝ, 0 < Γ ∧ ∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling)) ‖x‖ : ℂ) := by
  obtain ⟨c, hc, T₁, hT₁, hinner⟩ := exists_core_profile_lower_of_radialData hr hRad hAcore
  obtain ⟨T₂, hT₂, houter⟩ := exists_radialCore_kernel_of_radialData hb hr hRad
  refine ⟨c, hc, max T₁ T₂, hT₁.trans_le (le_max_left _ _), ?_⟩
  intro coupling hcoupling
  obtain ⟨φ, hφ, hpos, hΓ⟩ := houter coupling ((le_max_right _ _).trans hcoupling)
  exact ⟨φ, hφ, hpos, hinner coupling ((le_max_left _ _).trans hcoupling) φ hφ hpos, hΓ⟩

end InfiniteZero
