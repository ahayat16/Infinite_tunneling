import InfiniteZero.AtomicAgmonWeight
import InfiniteZero.AtomicAgmonRegion
import InfiniteZero.MagneticAgmonBounded
import InfiniteZero.MagneticBoundedPerturbation

/-!
# Global exterior decay for genuine atomic eigenfunctions

A fixed bounded weight gives exponential decay beyond radius `4 r₀`.
The constants are fixed before the coupling, energy and eigenfunction.
All integrability follows from L² and bounded multipliers; no global
differential energy integral is assumed. Both the radial core and the
actual nonradial potential are covered by the final specializations.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

private theorem atomicOuterCutoff_abs_le (p : CuspParameters) (hr₀ : 0 < p.r₀)
    (x : Plane) : |atomicOuterCutoff p hr₀ x| ≤ 1 :=
  Real.abs_cos_le_one _

private theorem atomicOuterCutoff_gradient_le_IMSError (p : CuspParameters)
    (hr₀ : 0 < p.r₀) (x : Plane) :
    cutoffGradientSq (atomicOuterCutoff p hr₀) x ≤
      magneticIMSError (atomicInnerCutoff p hr₀) (atomicOuterCutoff p hr₀) x := by
  unfold cutoffGradientSq magneticIMSError
  apply Finset.sum_le_sum
  intro i _
  exact le_add_of_nonneg_left (sq_nonneg _)

private theorem atomicAgmon_multiplier_bound (p : CuspParameters) (hr₀ : 0 < p.r₀)
    {coupling : ℝ} (hc : 0 ≤ coupling) (x : Plane) :
    |atomicOuterCutoff p hr₀ x * Real.exp (atomicAgmonWeight p hr₀ coupling x)| ≤
      Real.exp (atomicAgmonRate p hr₀ * coupling) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (atomicAgmonWeight p hr₀ coupling x) := by
      simpa using mul_le_mul_of_nonneg_right (atomicOuterCutoff_abs_le p hr₀ x)
        (Real.exp_pos _).le
    _ ≤ _ := Real.exp_le_exp.mpr (atomicAgmonWeight_le p hr₀ hc x)

/-- The actual tail is controlled by the actual weighted mass. -/
theorem atomicAgmon_exp_mul_tail_le_mass (p : CuspParameters) (hr₀ : 0 < p.r₀)
    {coupling : ℝ} (hc : 0 ≤ coupling) {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    Real.exp (2 * atomicAgmonRate p hr₀ * coupling) *
        (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
      mass (fun x => ((atomicOuterCutoff p hr₀ x *
        Real.exp (atomicAgmonWeight p hr₀ coupling x) : ℝ) : ℂ) * φ x) := by
  let w : Plane → ℝ := fun x => atomicOuterCutoff p hr₀ x *
    Real.exp (atomicAgmonWeight p hr₀ coupling x)
  have hw : Continuous w := (atomicOuterCutoff_contDiff p hr₀).continuous.mul
    (atomicAgmonWeight_contDiff p hr₀ coupling).exp.continuous
  have hLp : MemLp (fun x => (w x : ℂ) * φ x) 2 volume :=
    memLp_boundedPotential_mul w hw (atomicAgmon_multiplier_bound p hr₀ hc) hφ
  have hi : Integrable (fun x => ‖(w x : ℂ) * φ x‖ ^ 2) := hLp.norm.integrable_sq
  have hS : MeasurableSet {x : Plane | 4 * p.r₀ ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have heq : (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖(w x : ℂ) * φ x‖ ^ 2) =
      Real.exp (2 * atomicAgmonRate p hr₀ * coupling) *
        (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hS
    intro x hx
    have hout : atomicOuterCutoff p hr₀ x = 1 :=
      atomicOuterCutoff_one hr₀ (by dsimp only [mem_setOf_eq] at hx; linarith)
    have hF := atomicAgmonWeight_eq_height hr₀ coupling hx
    simp only [w, hout, hF, one_mul, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have hexp : Real.exp (2 * (atomicAgmonRate p hr₀ * coupling)) =
        Real.exp (atomicAgmonRate p hr₀ * coupling) ^ 2 := by
      simpa only [Nat.cast_ofNat] using
        Real.exp_nat_mul (atomicAgmonRate p hr₀ * coupling) 2
    rw [show 2 * atomicAgmonRate p hr₀ * coupling =
      2 * (atomicAgmonRate p hr₀ * coupling) by ring, hexp]
  rw [← heq]
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun x => sq_nonneg _)

/-- A fixed coefficient controls weighted mass uniformly in the field,
coupling, energy and state whenever the displayed exterior reserve holds. -/
theorem exists_atomicAgmon_weighted_mass_bound (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ∃ C > 0, ∀ (b coupling E : ℝ) (V : Potential) (φ : Wavefunction),
      0 < coupling → Continuous V → IsEigenfunction b coupling V E φ → mass φ = 1 →
      (∀ x : Plane, p.r₀ ≤ ‖x‖ → coupling ^ 2 / 4 ≤ coupling ^ 2 * V x - E) →
      mass (fun x => ((atomicOuterCutoff p hr₀ x *
        Real.exp (atomicAgmonWeight p hr₀ coupling x) : ℝ) : ℂ) * φ x) ≤ C / coupling ^ 2 := by
  obtain ⟨C₀, hC₀, hIMS⟩ := exists_atomicIMSError_bound p hr₀
  have hgrad (x : Plane) : cutoffGradientSq (atomicOuterCutoff p hr₀) x ≤ C₀ :=
    (atomicOuterCutoff_gradient_le_IMSError p hr₀ x).trans (hIMS x)
  refine ⟨16 * C₀, by positivity, ?_⟩
  intro b coupling E V φ hc hV hφ hmass hreserve
  have hr : ∀ x, atomicOuterCutoff p hr₀ x ≠ 0 →
      coupling ^ 2 / 8 ≤ coupling ^ 2 * V x - E -
        2 * cutoffGradientSq (atomicAgmonWeight p hr₀ coupling) x := by
    intro x hx
    have hxout : p.r₀ ≤ ‖x‖ := by
      by_contra hn
      exact hx (atomicOuterCutoff_zero hr₀ (by linarith))
    have hres := hreserve x hxout
    have hg := atomicAgmonWeight_gradient_le p hr₀ hc.le x
    linarith
  have hAg := magnetic_agmon_bounded_weight hV (atomicOuterCutoff_contDiff p hr₀)
    (atomicOuterCutoff_abs_le p hr₀) hC₀.le hgrad
    (atomicAgmonWeight_contDiff p hr₀ coupling) (atomicAgmonWeight_le p hr₀ hc.le) hφ hr
  simp_rw [exp_atomicAgmonWeight_sq_mul_outer_gradient] at hAg
  have hi : Integrable (fun x => cutoffGradientSq (atomicOuterCutoff p hr₀) x *
      ‖φ x‖ ^ 2) := by
    apply hφ.2.1.norm.integrable_sq.bdd_mul
      (continuous_cutoffGradientSq (atomicOuterCutoff_contDiff p hr₀)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (cutoffGradientSq_nonneg _ _)] using hgrad x
  have hint : (∫ x : Plane, cutoffGradientSq (atomicOuterCutoff p hr₀) x * ‖φ x‖ ^ 2) ≤ C₀ := by
    have hh := integral_mono hi (hφ.2.1.norm.integrable_sq.const_mul C₀)
      (fun x => mul_le_mul_of_nonneg_right (hgrad x) (sq_nonneg _))
    rw [integral_const_mul] at hh
    change (∫ x : Plane, cutoffGradientSq (atomicOuterCutoff p hr₀) x * ‖φ x‖ ^ 2) ≤
      C₀ * mass φ at hh
    simpa only [hmass, mul_one] using hh
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  nlinarith only [hAg, hint]

/-- A generic global bound with a concrete fixed rate and explicit exterior
reserve, ready for specialization to the two actual atomic potentials. -/
theorem exists_atomicAgmon_tail_bound (p : CuspParameters) (hr₀ : 0 < p.r₀) :
    ∃ C > 0, ∃ d > 0, ∀ (b coupling E : ℝ) (V : Potential) (φ : Wavefunction),
      0 < coupling → Continuous V → IsEigenfunction b coupling V E φ → mass φ = 1 →
      (∀ x : Plane, p.r₀ ≤ ‖x‖ → coupling ^ 2 / 4 ≤ coupling ^ 2 * V x - E) →
      (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
        (C / coupling ^ 2) * Real.exp (-2 * d * coupling) := by
  obtain ⟨C, hC, hmass⟩ := exists_atomicAgmon_weighted_mass_bound p hr₀
  refine ⟨C, hC, atomicAgmonRate p hr₀, atomicAgmonRate_pos p hr₀, ?_⟩
  intro b coupling E V φ hc hV hφ hn hreserve
  have hm := hmass b coupling E V φ hc hV hφ hn hreserve
  have ht := atomicAgmon_exp_mul_tail_le_mass p hr₀ hc.le hφ.2.1
  have hb := ht.trans hm
  have he : Real.exp (2 * atomicAgmonRate p hr₀ * coupling) > 0 := Real.exp_pos _
  have hb' : (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
      (C / coupling ^ 2) / Real.exp (2 * atomicAgmonRate p hr₀ * coupling) := by
    apply (le_div_iff₀ he).mpr
    simpa only [mul_comm] using hb
  calc
    _ ≤ (C / coupling ^ 2) / Real.exp (2 * atomicAgmonRate p hr₀ * coupling) := hb'
    _ = _ := by rw [show -2 * atomicAgmonRate p hr₀ * coupling =
      -(2 * atomicAgmonRate p hr₀ * coupling) by ring, Real.exp_neg, div_eq_mul_inv]

/-- Exponential exterior probability for every normalized low-energy
eigenfunction of the actual constructed potential. -/
theorem exists_atomicPotential_agmon_tail {p : CuspParameters} (hp : p.BasicConditions) :
    ∃ C > 0, ∃ d > 0, ∀ coupling : ℝ, 0 < coupling → ∀ E : ℝ,
      E ≤ -(3 / 4 : ℝ) * coupling ^ 2 → ∀ φ : Wavefunction,
      IsEigenfunction p.b coupling p.potential E φ → mass φ = 1 →
      (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
        (C / coupling ^ 2) * Real.exp (-2 * d * coupling) := by
  obtain ⟨C, hC, d, hd, hbound⟩ := exists_atomicAgmon_tail_bound p hp.r₀_pos
  refine ⟨C, hC, d, hd, ?_⟩
  intro coupling hc E hE φ hφ hm
  exact hbound p.b coupling E p.potential φ hc (potential_contDiff hp).continuous hφ hm
    (fun x hx => potential_exterior_spectral_reserve hp hE hx)

/-- The same actual integral estimate for the radial reference ground-state
problem; only the core radius is assumed positive. -/
theorem exists_atomicCore_agmon_tail {p : CuspParameters} (hr₀ : 0 < p.r₀) :
    ∃ C > 0, ∃ d > 0, ∀ (b coupling : ℝ), 0 < coupling → ∀ E : ℝ,
      E ≤ -(3 / 4 : ℝ) * coupling ^ 2 → ∀ φ : Wavefunction,
      IsEigenfunction b coupling p.core E φ → mass φ = 1 →
      (∫ x in {x : Plane | 4 * p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
        (C / coupling ^ 2) * Real.exp (-2 * d * coupling) := by
  obtain ⟨C, hC, d, hd, hbound⟩ := exists_atomicAgmon_tail_bound p hr₀
  refine ⟨C, hC, d, hd, ?_⟩
  intro b coupling hc E hE φ hφ hm
  apply hbound b coupling E p.core φ hc (core_contDiff hr₀).continuous hφ hm
  intro x hx
  have hz : p.core x = 0 := by simp [core, not_lt.mpr hx]
  rw [hz, mul_zero, zero_sub]
  nlinarith [sq_nonneg coupling]

end InfiniteZero.CuspParameters
