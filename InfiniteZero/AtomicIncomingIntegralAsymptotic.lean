import InfiniteZero.IncomingCuspTangentialIntegration
import InfiniteZero.AtomicIncomingNormalAsymptotic

/-!
# Leading asymptotic of the full incoming cusp integral

The proved uniform two-normal asymptotic integrates over the fixed real
tangent rectangle. The leading coefficient is the square of the cutoff
mass times the complex normal saddle value; no conjugation of one normal
factor is introduced. The physical kernel normalization retains the true
core and full energies throughout.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem incomingCusp_leading_coefficient_ne_zero
    {p : CuspParameters} (hp : p.BasicConditions) :
    (p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ) * (p.cuspTangentialMass ^ 2 : ℝ) ≠ 0 := by
  have ht : (p.tStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (hp.t₀_pos.trans hp.t₀_lt).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hβ : (p.β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.β_pos.ne'
  have hm : ((p.cuspTangentialMass ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (cuspTangentialMass_pos hp).ne')
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 6 ht) (div_ne_zero hπ hβ)) hm

theorem tendsto_atomic_incomingCuspIntegral_normalized_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    Tendsto (fun h : ℝ =>
      let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
      let Ef := scaledAtomicEnergy p h⁻¹
      logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
        p.incomingCuspNormalization L h Ec Ef * p.incomingCuspIntegral L h Ec Ef)
      (𝓝[>] 0)
      (𝓝 ((p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ) * (p.cuspTangentialMass ^ 2 : ℝ))) := by
  obtain ⟨T, _hT, henergies⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let area : ℝ := (2 * p.s₀) ^ 2
  have harea : 0 ≤ area := sq_nonneg _
  let δ := ε / (area + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [eventually_atomic_incomingCuspNormal_leading_uniform_of_radialData
      hp hRad hAcore hApot hL hδ,
    tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T),
    self_mem_nhdsWithin] with h hnormal hT hh
  let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
  let Ef := scaledAtomicEnergy p h⁻¹
  let Z := logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
    p.incomingCuspNormalization L h Ec Ef
  let a : ℂ := (p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ)
  have hE := henergies h⁻¹ hT
  simp only [inv_inv] at hE
  have hEc : 0 < Ec := lt_of_lt_of_le (by norm_num) hE.2.1.1
  have hEf : 0 < Ef := lt_of_lt_of_le (by norm_num) hE.1.1
  have hbound := norm_incomingCuspIntegral_sub_tangential_le hp hL hh hEc hEf Z a hδ.le
    (fun s hs r hr => by
      have hn := hnormal s r (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)
        (abs_le.mpr ⟨hr.1.le, hr.2.le⟩)
      simpa only [Z, a, Ec, Ef, incomingCuspNormalIntegral, mul_assoc, mul_comm,
        mul_left_comm] using hn.le)
  have hsmall : δ * area < ε := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (show 0 < area + 1 by positivity)).mpr
    nlinarith
  simpa only [dist_eq_norm, Z, a, Ec, Ef, area] using hbound.trans_lt hsmall

theorem tendsto_atomic_incomingCuspIntegral_relative_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    Tendsto (fun h : ℝ =>
      let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
      let Ef := scaledAtomicEnergy p h⁻¹
      (logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
        p.incomingCuspNormalization L h Ec Ef * p.incomingCuspIntegral L h Ec Ef) /
        ((p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ) * (p.cuspTangentialMass ^ 2 : ℝ)))
      (𝓝[>] 0) (𝓝 1) := by
  have hlim :=
    (tendsto_atomic_incomingCuspIntegral_normalized_of_radialData hp hRad hAcore hApot hL).div_const
      ((p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ) * (p.cuspTangentialMass ^ 2 : ℝ))
  have hne := incomingCusp_leading_coefficient_ne_zero hp
  rw [div_self hne] at hlim
  exact hlim

end InfiniteZero.CuspParameters
