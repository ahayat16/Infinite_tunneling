import InfiniteZero.AtomicGroundEnergyBounds
import InfiniteZero.MagneticAgmonWeighted

/-!
# The forbidden region of the actual nonradial atomic potential

Outside the radial core, the concrete cusp depth leaves a reserve of order
coupling squared. The energy condition used in the local estimate is proved
eventually from the radial input, not an extra nonradial spectral assumption.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InfiniteZero.CuspParameters

theorem potential_exterior_spectral_reserve {p : CuspParameters}
    (hp : p.BasicConditions) {coupling E : ℝ}
    (hE : E ≤ -(3 / 4 : ℝ) * coupling ^ 2) {x : Plane} (hx : p.r₀ ≤ ‖x‖) :
    coupling ^ 2 / 4 ≤ coupling ^ 2 * p.potential x - E := by
  have hv := potential_exterior_gt_neg_half hp hx
  have hm := mul_le_mul_of_nonneg_left hv.le (sq_nonneg coupling)
  nlinarith only [hm, hE]

theorem exists_atomic_exterior_reserve_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ x : Plane, p.r₀ ≤ ‖x‖ →
        coupling ^ 2 / 4 ≤ coupling ^ 2 * p.potential x -
          atomicGroundEnergy p.b p.potential coupling := by
  obtain ⟨T, hT, hbound⟩ := exists_atomicGroundEnergy_bounds_of_radialData hp hRad hAcore hApot
  refine ⟨max T (4 * hRad.energyBound), hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc x hx
  have hcT := (le_max_left T (4 * hRad.energyBound)).trans hc
  have hcB := (le_max_right T (4 * hRad.energyBound)).trans hc
  have hcpos : 0 < coupling := hT.trans_le hcT
  have he := (hbound coupling hcT).2
  have hm := mul_le_mul_of_nonneg_right hcB hcpos.le
  apply potential_exterior_spectral_reserve hp (x := x) ?_ hx
  nlinarith only [he, hm]

/-- Actual eigenfunctions satisfy the exterior cutoff estimate. The cutoff
may meet either cusp; only its vanishing on the radial core is needed. -/
theorem atomic_exterior_cutoff_estimate {p : CuspParameters} (hp : p.BasicConditions)
    {coupling E : ℝ} {φ : Wavefunction} {χ : Plane → ℝ}
    (hE : E ≤ -(3 / 4 : ℝ) * coupling ^ 2)
    (hφ : IsEigenfunction p.b coupling p.potential E φ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (houtside : ∀ x, χ x ≠ 0 → p.r₀ ≤ ‖x‖) :
    coupling ^ 2 / 4 * mass (fun x => (χ x : ℂ) * φ x) ≤
      ∫ x : Plane, cutoffGradientSq χ x * ‖φ x‖ ^ 2 :=
  cutoff_mass_le_gradient_error (potential_contDiff hp).continuous hχ hc hφ
    (fun x hx => potential_exterior_spectral_reserve hp hE (houtside x hx))

/-- A smooth exponential weight whose squared gradient is at most λ²/16
leaves a coercive reserve λ²/8 on the actual forbidden region. The estimate
holds for arbitrary compact exterior cutoffs, including across the cusps. -/
theorem atomic_weighted_exterior_cutoff_estimate {p : CuspParameters}
    (hp : p.BasicConditions) {coupling E : ℝ} {φ : Wavefunction} {η F : Plane → ℝ}
    (hE : E ≤ -(3 / 4 : ℝ) * coupling ^ 2)
    (hφ : IsEigenfunction p.b coupling p.potential E φ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hF : ContDiff ℝ ∞ F)
    (houtside : ∀ x, η x ≠ 0 → p.r₀ ≤ ‖x‖)
    (hgradient : ∀ x, η x ≠ 0 → cutoffGradientSq F x ≤ coupling ^ 2 / 16) :
    coupling ^ 2 / 8 * mass (fun x => ((η x * Real.exp (F x) : ℝ) : ℂ) * φ x) ≤
      2 * ∫ x : Plane, Real.exp (F x) ^ 2 * cutoffGradientSq η x * ‖φ x‖ ^ 2 := by
  apply weighted_cutoff_mass_le_gradient_error (potential_contDiff hp).continuous hη hc hF hφ
  intro x hx
  have hr := potential_exterior_spectral_reserve hp hE (houtside x hx)
  have hg := hgradient x hx
  linarith

end InfiniteZero.CuspParameters
