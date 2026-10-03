import InfiniteZero.IncomingCuspDensityNormalization

/-!
# Bounds for the physical incoming normalization

The magnetic constant phase has unit modulus. After cancelling the real
action, the normalization is just the cube of `h^(3/2)` divided by the
positive product of three leading kernel coefficients. Convergence of
the two actual energies to one bounds that denominator away from zero.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem norm_incomingCuspNormalization {p : CuspParameters} (hp : p.BasicConditions)
    {L h Ecore Efull : ℝ} (hL : p.R < 2 * L) (hh : 0 ≤ h)
    (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    ‖p.incomingCuspNormalization L h Ecore Efull‖ =
      (h ^ (3 / 2 : ℝ)) ^ 3 /
        (landauLeadingCoefficient p.b Ecore p.R ^ 2 *
          landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L)) *
      Real.exp (p.activeReferenceAction L Efull Ecore / h) := by
  have hkR := landauLeadingCoefficient_pos hp.b_pos hEc hp.radius_pos
  have hkD := landauLeadingCoefficient_pos hp.b_pos hEf (Geometry.activeDistance_pos hL)
  simp [incomingCuspNormalization, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hh (3 / 2 : ℝ)),
    abs_of_pos hkR, abs_of_pos hkD, Complex.norm_exp, Complex.div_ofReal_re]

theorem norm_incomingCuspNormalization_mul_exp_neg_action
    {p : CuspParameters} (hp : p.BasicConditions)
    {L h Ecore Efull : ℝ} (hL : p.R < 2 * L) (hh : 0 ≤ h)
    (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    ‖p.incomingCuspNormalization L h Ecore Efull‖ *
        Real.exp (-p.activeReferenceAction L Efull Ecore / h) =
      (h ^ (3 / 2 : ℝ)) ^ 3 /
        (landauLeadingCoefficient p.b Ecore p.R ^ 2 *
          landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L)) := by
  rw [norm_incomingCuspNormalization hp hL hh hEc hEf, mul_assoc, ← Real.exp_add]
  simp [neg_div]

/-- Two arbitrary energy functions converging to one suffice. No convergence
rate, source estimate, or relation between the energies is required. -/
theorem exists_incomingCuspNormalization_action_bound
    {p : CuspParameters} (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L)
    {Ecore Efull : ℝ → ℝ}
    (hEc : Tendsto Ecore (𝓝[>] 0) (𝓝 1))
    (hEf : Tendsto Efull (𝓝[>] 0) (𝓝 1)) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖p.incomingCuspNormalization L h (Ecore h) (Efull h)‖ *
        Real.exp (-p.activeReferenceAction L (Efull h) (Ecore h) / h) ≤ C := by
  let K₀ := landauLeadingCoefficient p.b 1 p.R ^ 2 *
    landauLeadingCoefficient p.b 1 (Geometry.activeDistance p.R L)
  have hkR := landauLeadingCoefficient_pos hp.b_pos (by norm_num : (0 : ℝ) < 1) hp.radius_pos
  have hkD := landauLeadingCoefficient_pos hp.b_pos (by norm_num : (0 : ℝ) < 1)
    (Geometry.activeDistance_pos hL)
  have hK₀ : 0 < K₀ := mul_pos (sq_pos_of_pos hkR) hkD
  have hcore := tendsto_landauLeadingCoefficient_parameters hp.b_pos
    (by norm_num : (0 : ℝ) < 1) hp.radius_pos hEc
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => p.R) (𝓝[>] 0) (𝓝 p.R))
  have hfull := tendsto_landauLeadingCoefficient_parameters hp.b_pos
    (by norm_num : (0 : ℝ) < 1) (Geometry.activeDistance_pos hL) hEf
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => Geometry.activeDistance p.R L)
      (𝓝[>] 0) (𝓝 (Geometry.activeDistance p.R L)))
  have hprod : Tendsto (fun h => landauLeadingCoefficient p.b (Ecore h) p.R ^ 2 *
      landauLeadingCoefficient p.b (Efull h) (Geometry.activeDistance p.R L))
      (𝓝[>] 0) (𝓝 K₀) := (hcore.pow 2).mul hfull
  refine ⟨2 / K₀, by positivity, ?_⟩
  filter_upwards [hprod.eventually (le_mem_nhds (half_lt_self hK₀)),
    hEc.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hEf.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with h hden hEcpos hEfpos hh hh1
  have hhpos : 0 < h := hh
  have hpow := Real.rpow_le_one hhpos.le hh1.le (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hnum : (h ^ (3 / 2 : ℝ)) ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (Real.rpow_nonneg hhpos.le _) hpow 3
  rw [norm_incomingCuspNormalization_mul_exp_neg_action hp hL hhpos.le hEcpos hEfpos]
  calc
    _ ≤ 1 / (landauLeadingCoefficient p.b (Ecore h) p.R ^ 2 *
        landauLeadingCoefficient p.b (Efull h) (Geometry.activeDistance p.R L)) :=
      div_le_div_of_nonneg_right hnum ((half_pos hK₀).le.trans hden)
    _ ≤ 1 / (K₀ / 2) := one_div_le_one_div_of_le (half_pos hK₀) hden
    _ = 2 / K₀ := by ring

/-- The true core and full atomic energies give a normalization constant
fixed before the small semiclassical parameter. -/
theorem exists_incomingCuspNormalization_action_bound_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖p.incomingCuspNormalization L h
        (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹)‖ *
      Real.exp (-p.activeReferenceAction L (scaledAtomicEnergy p h⁻¹)
        (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) / h) ≤ C :=
  exists_incomingCuspNormalization_action_bound hp hL
    (tendsto_semiclassicalCoreEnergy_of_radialData hp hRad hAcore hApot)
    ((tendsto_scaledAtomicEnergy_of_radialData hp hRad hAcore hApot).comp
      tendsto_inv_nhdsGT_zero)

theorem exists_incomingCuspNormalization_norm_bound_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖p.incomingCuspNormalization L h
        (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) (scaledAtomicEnergy p h⁻¹)‖ ≤
      C * Real.exp (p.activeReferenceAction L (scaledAtomicEnergy p h⁻¹)
        (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) / h) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_incomingCuspNormalization_action_bound_of_radialData hp hRad hAcore hApot hL
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with h hh
  have hb := mul_le_mul_of_nonneg_right hh
    (Real.exp_pos (p.activeReferenceAction L (scaledAtomicEnergy p h⁻¹)
      (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)) / h)).le
  simpa only [mul_assoc, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one] using hb

end InfiniteZero.CuspParameters
