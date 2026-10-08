import InfiniteZero.AtomicIncomingRealTruncation
import InfiniteZero.IncomingCuspLogarithmicChange
import InfiniteZero.AtomicCuspContourTranslation
import InfiniteZero.CuspSaddleLeading

/-!
# Leading asymptotic of the actual incoming normal integral

This assembly uses the true core/full energies, the physical density,
its real truncation, the exact logarithmic Jacobians, both contour shifts,
and the evaluated product saddle with its actual kernel multiplier.
The result is uniform in the two real tangent variables.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace InfiniteZero.CuspParameters

theorem eventually_atomic_incomingCusp_active_logarithmic_identity_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
      let Ef := scaledAtomicEnergy p h⁻¹
      p.incomingCuspNormalization L h Ec Ef *
        (∫ q in positiveNormalBox (logFlatActiveWindow p.tStar h),
          p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) =
        ((p.χb s * p.χb r : ℝ) : ℂ) * (p.tStar : ℂ) ^ 6 *
          p.atomicCuspLogDoubleIntegral L h s r 0 0 := by
  obtain ⟨T, _hT, henergies⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  filter_upwards [eventually_incomingCuspDensity_active_logarithmic_change hp hL,
    eventually_integrableOn_atomicCuspLogProduct_of_radialData hp hRad hAcore hApot hL,
    tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T)] with h hchange hint hT
  intro s r hs hr
  have hE := henergies h⁻¹ hT
  simp only [inv_inv] at hE
  have hEc : 0 < -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹) := by linarith [hE.2.1.1]
  have hEf : 0 < scaledAtomicEnergy p h⁻¹ := by linarith [hE.1.1]
  have hfub := setIntegral_prod _ (hint s r hs hr 0 left_mem_uIcc 0 left_mem_uIcc)
  have hid := hchange _ hEc _ hEf s r hs hr
  dsimp only
  rw [atomicCuspLogDoubleIntegral, hfub]
  simpa only [atomicCuspLogProduct, Complex.ofReal_zero, zero_mul, add_zero] using hid

/-- The full physical two-normal integral has its explicit scalar leading
value times the two tangent cutoffs. No incoming estimate
or contour identity is left as an assumption. -/
theorem eventually_atomic_incomingCuspNormal_leading_uniform_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
      let Ef := scaledAtomicEnergy p h⁻¹
      ‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
        (p.incomingCuspNormalization L h Ec Ef *
          (∫ q in positiveNormalBox p.t₀, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r)) -
        ((p.χb s * p.χb r : ℝ) : ℂ) * (p.tStar : ℂ) ^ 6 * (Real.pi / p.β : ℂ)‖ < ε := by
  let M := p.tStar ^ 6
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ := ε / (3 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [eventually_atomic_incomingCusp_normalized_truncation_of_radialData
      hp hRad hAcore hApot hL hδ,
    eventually_atomic_incomingCusp_active_logarithmic_identity_of_radialData
      hp hRad hAcore hApot hL,
    eventually_atomicCuspLogDoubleIntegral_shift_error_of_radialData
      hp hRad hAcore hApot hL hδ,
    eventually_atomicCuspSaddleProduct_leading_uniform_of_radialData
      hp hRad hAcore hApot hL hδ] with h htail hchange hshift hlead
  intro s r hs hr
  let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
  let Ef := scaledAtomicEnergy p h⁻¹
  let N := logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h
  let Z := p.incomingCuspNormalization L h Ec Ef
  let X := ∫ q in positiveNormalBox p.t₀, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r
  let Y := ∫ q in positiveNormalBox (logFlatActiveWindow p.tStar h),
    p.incomingCuspDensity L h Ec Ef q.1 q.2 s r
  let v := (logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h).im
  let I₀ := p.atomicCuspLogDoubleIntegral L h s r 0 0
  let Iᵥ := p.atomicCuspLogDoubleIntegral L h s r v v
  let K : ℂ := ((p.χb s * p.χb r : ℝ) : ℂ) * (p.tStar : ℂ) ^ 6
  have hK : ‖K‖ ≤ M := by
    have hcutpos := mul_nonneg (hp.χb_range s).1 (hp.χb_range r).1
    have hcut : p.χb s * p.χb r ≤ 1 := by
      nlinarith [(hp.χb_range s).1, (hp.χb_range s).2,
        (hp.χb_range r).1, (hp.χb_range r).2]
    dsimp only [K, M]
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcutpos,
      abs_of_pos (hp.t₀_pos.trans hp.t₀_lt)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcut (pow_nonneg
      (hp.t₀_pos.trans hp.t₀_lt).le 6)
  have hT : ‖N ^ 2 * (Z * (X - Y))‖ < δ := htail s r hs hr
  have hC : Z * Y = K * I₀ := hchange s r hs hr
  have hD : ‖N ^ 2 * (I₀ - Iᵥ)‖ < δ := hshift s r hs hr
  have hS : ‖N ^ 2 * Iᵥ - (Real.pi / p.β : ℂ)‖ < δ := by
    simpa only [N, Iᵥ, v, atomicCuspLogDoubleIntegral_saddle_eq, Complex.ofReal_div]
      using hlead s r hs hr
  have hB : ‖K * (N ^ 2 * (I₀ - Iᵥ))‖ ≤ M * δ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hD.le (norm_nonneg K)).trans
      (mul_le_mul_of_nonneg_right hK hδ.le)
  have hG : ‖K * (N ^ 2 * Iᵥ - (Real.pi / p.β : ℂ))‖ ≤ M * δ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hS.le (norm_nonneg K)).trans
      (mul_le_mul_of_nonneg_right hK hδ.le)
  have he : N ^ 2 * (Z * X) - K * (Real.pi / p.β : ℂ) =
      N ^ 2 * (Z * (X - Y)) + K * (N ^ 2 * (I₀ - Iᵥ)) +
        K * (N ^ 2 * Iᵥ - (Real.pi / p.β : ℂ)) := by
    calc
      _ = N ^ 2 * (Z * (X - Y)) +
          (N ^ 2 * (Z * Y) - K * (Real.pi / p.β : ℂ)) := by ring
      _ = _ := by rw [hC]; ring
  have hsmall : δ + M * δ + M * δ < ε := by
    dsimp [δ]
    field_simp
    nlinarith
  change ‖N ^ 2 * (Z * X) - K * (Real.pi / p.β : ℂ)‖ < ε
  rw [he]
  calc
    _ ≤ ‖N ^ 2 * (Z * (X - Y)) + K * (N ^ 2 * (I₀ - Iᵥ))‖ +
        ‖K * (N ^ 2 * Iᵥ - (Real.pi / p.β : ℂ))‖ := norm_add_le _ _
    _ ≤ (‖N ^ 2 * (Z * (X - Y))‖ + ‖K * (N ^ 2 * (I₀ - Iᵥ))‖) +
        ‖K * (N ^ 2 * Iᵥ - (Real.pi / p.β : ℂ))‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ δ + M * δ + M * δ := add_le_add (add_le_add hT.le hB) hG
    _ < ε := hsmall

end InfiniteZero.CuspParameters
