import InfiniteZero.AtomicGroundConstruction
import InfiniteZero.HoppingChannels

/-!
# Energy bounds for the constructed atomic ground state

The lower bound uses only nonnegative magnetic kinetic energy and the actual
potential bound `V ≥ −1`. The upper bound follows from the constructed ground
state and the radial reference energy. In particular, no separate positivity
assumption is needed for the scaled energy entering the Landau kernel.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace InfiniteZero

theorem magneticForm_lower_of_potential_ge_neg_one {b coupling : ℝ}
    {V : Potential} (hV : Continuous V) (hVlower : ∀ x, -1 ≤ V x)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    -coupling ^ 2 * mass ψ ≤ magneticForm b coupling V ψ := by
  have hpoint (x : Plane) :
      -coupling ^ 2 * ‖ψ x‖ ^ 2 ≤ magneticEnergyDensity b coupling V ψ x := by
    have hkin : 0 ≤ ∑ i : Fin 2, ‖covariantDerivative b coupling i ψ x‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hpot := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hVlower x) (sq_nonneg coupling)) (sq_nonneg ‖ψ x‖)
    unfold magneticEnergyDensity
    nlinarith only [hkin, hpot]
  have hint := integral_mono (hψ.integrable_norm_sq.const_mul (-coupling ^ 2))
    (hψ.integrable_magneticEnergyDensity b coupling hV) hpoint
  simpa only [integral_const_mul, mass, magneticForm_eq_integral_density] using hint

/-- The same lower bound on the actual closed operator domain. -/
theorem IsMagneticRealization.lower_of_potential_ge_neg_one {b coupling : ℝ}
    {V : Potential} (hA : IsMagneticRealization b coupling V)
    (hV : Continuous V) (hVlower : ∀ x, -1 ≤ V x)
    (u : (magneticOperator b coupling V).domain) :
    -coupling ^ 2 * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (magneticOperator b coupling V u)).re := by
  have hz : MemLp (0 : Wavefunction) 2 volume := MemLp.zero
  have hbound (ψ : Wavefunction) (hψ : IsTestFunction ψ) :
      0 * mass ψ - 0 * ‖waveInner 0 ψ‖ ^ 2 ≤
        magneticForm b coupling V ψ - (-coupling ^ 2) * mass ψ := by
    have h := magneticForm_lower_of_potential_ge_neg_one
      (b := b) (coupling := coupling) hV hVlower hψ
    linarith
  have h := hA.rankOne_lower hV hz hbound u
  simpa only [zero_mul, sub_zero, sub_nonneg] using h

namespace CuspParameters

theorem exists_atomicGroundEnergy_bounds_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      -coupling ^ 2 ≤ atomicGroundEnergy p.b p.potential coupling ∧
      atomicGroundEnergy p.b p.potential coupling ≤
        -coupling ^ 2 + hRad.energyBound * coupling := by
  obtain ⟨T, hT, hcert⟩ := exists_atomicGroundCertificate_of_radialData hp hRad hAcore hApot
  refine ⟨max T hRad.threshold, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcT := (le_max_left T hRad.threshold).trans hc
  have hcRad := (le_max_right T hRad.threshold).trans hc
  have hcpos : 0 < coupling := hT.trans_le hcT
  obtain ⟨E, hE, c, _⟩ := hcert coupling hcT
  have heq := (hApot coupling).atomicGroundEnergy_eq_of_certificate c
  constructor
  · have h := (hApot coupling).lower_of_potential_ge_neg_one
      (potential_contDiff hp).continuous (fun x => (potential_range hp x).1) c.normalizedVector
    rw [re_inner_eq_of_operator_eigenvector _ E _ c.normalizedVector_eigenvector,
      c.normalizedVector_norm] at h
    simpa only [one_pow, mul_one, heq] using h
  · obtain ⟨φ, hφ, hupper, _⟩ := hRad.ground coupling hcRad
    have hscaled := mul_le_mul_of_nonneg_left hupper (sq_nonneg coupling)
    have hcancel : coupling ^ 2 * ((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling) =
        atomicGroundEnergy p.b p.core coupling := by field_simp
    have hright : coupling ^ 2 * (-1 + hRad.energyBound / coupling) =
        -coupling ^ 2 + hRad.energyBound * coupling := by field_simp
    change coupling ^ 2 * ((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling) ≤
      coupling ^ 2 * (-1 + hRad.energyBound / coupling) at hscaled
    rw [hcancel, hright] at hscaled
    exact heq.trans_le (hE.trans hscaled)

theorem exists_scaledAtomicEnergy_bounds_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      1 - hRad.energyBound / coupling ≤ scaledAtomicEnergy p coupling ∧
      scaledAtomicEnergy p coupling ≤ 1 := by
  obtain ⟨T, hT, hbound⟩ := exists_atomicGroundEnergy_bounds_of_radialData hp hRad hAcore hApot
  refine ⟨T, hT, ?_⟩
  intro coupling hc
  have hcpos : 0 < coupling := hT.trans_le hc
  obtain ⟨hlower, hupper⟩ := hbound coupling hc
  have hcancel : (coupling⁻¹) ^ 2 * coupling ^ 2 = 1 := by field_simp
  have hlinear : (coupling⁻¹) ^ 2 * (hRad.energyBound * coupling) =
      hRad.energyBound / coupling := by field_simp
  have hlo := mul_le_mul_of_nonneg_left hlower (sq_nonneg (coupling⁻¹))
  have hup := mul_le_mul_of_nonneg_left hupper (sq_nonneg (coupling⁻¹))
  simp only [mul_add, mul_neg, hcancel, hlinear] at hlo hup
  unfold scaledAtomicEnergy
  constructor <;> nlinarith only [hlo, hup]

theorem tendsto_scaledAtomicEnergy_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    Tendsto (scaledAtomicEnergy p) atTop (𝓝 1) := by
  obtain ⟨T, _, hbound⟩ := exists_scaledAtomicEnergy_bounds_of_radialData hp hRad hAcore hApot
  have hlo : Tendsto (fun coupling : ℝ => 1 - hRad.energyBound / coupling) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_id.const_div_atTop hRad.energyBound))
  exact hlo.squeeze' tendsto_const_nhds
    ((eventually_ge_atTop T).mono fun coupling hc => (hbound coupling hc).1)
    ((eventually_ge_atTop T).mono fun coupling hc => (hbound coupling hc).2)

/-- A single threshold supplies the concrete positive energy range used by
the Landau kernel and by `Main`'s channel construction. -/
theorem exists_scaledAtomicEnergy_pos_of_radialData {p : CuspParameters}
    (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      (1 / 2 : ℝ) ≤ scaledAtomicEnergy p coupling ∧
      0 < scaledAtomicEnergy p coupling ∧ scaledAtomicEnergy p coupling ≤ 1 := by
  obtain ⟨T, hT, hbound⟩ := exists_scaledAtomicEnergy_bounds_of_radialData hp hRad hAcore hApot
  refine ⟨max T (2 * hRad.energyBound), hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hcT := (le_max_left T (2 * hRad.energyBound)).trans hc
  have hcB := (le_max_right T (2 * hRad.energyBound)).trans hc
  have hcpos : 0 < coupling := hT.trans_le hcT
  obtain ⟨hlower, hupper⟩ := hbound coupling hcT
  have hdiv : hRad.energyBound / coupling ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hcpos).mpr
    linarith
  refine ⟨by linarith, by linarith, hupper⟩

end CuspParameters
end InfiniteZero
