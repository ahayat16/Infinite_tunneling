import InfiniteZero.IncomingCuspNormalizationBounds
import InfiniteZero.IncomingCuspRealTruncation

/-!
# Real truncation with the physical incoming normalization

The true core and full energies are retained. The normalizer bound absorbs
the kernel coefficients and the constant magnetic phase, so the real tail
is negligible with the same physical normalization used on the active cell.
The small-parameter threshold is uniform in both tangential coordinates.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem eventually_atomic_incomingCusp_normalized_truncation_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : p.R < 2 * L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
      let Ef := scaledAtomicEnergy p h⁻¹
      ‖logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2 *
        (p.incomingCuspNormalization L h Ec Ef *
          ((∫ q in positiveNormalBox p.t₀, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) -
            (∫ q in positiveNormalBox (logFlatActiveWindow p.tStar h),
              p.incomingCuspDensity L h Ec Ef q.1 q.2 s r)))‖ < ε := by
  obtain ⟨C, hC, hnormal⟩ :=
    exists_incomingCuspNormalization_action_bound_of_radialData hp hRad hAcore hApot hL
  obtain ⟨T, _hT, henergies⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  have hsmall := eventually_incomingCuspDensity_action_normalized_truncation hp hL
    (div_pos hε (show 0 < C + 1 by linarith))
  filter_upwards [hnormal, hsmall,
    tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T)] with h hn hsml hT
  intro s r hs hr
  dsimp only
  let Ec := -(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹)
  let Ef := scaledAtomicEnergy p h⁻¹
  let A := p.activeReferenceAction L Ef Ec / h
  let Z := logFlatSaddleNormalizer p.β 2 p.tStar (p.activeSaddleSlope L) h ^ 2
  let D := (∫ q in positiveNormalBox p.t₀, p.incomingCuspDensity L h Ec Ef q.1 q.2 s r) -
    (∫ q in positiveNormalBox (logFlatActiveWindow p.tStar h),
      p.incomingCuspDensity L h Ec Ef q.1 q.2 s r)
  have hE := henergies h⁻¹ hT
  simp only [inv_inv] at hE
  have heps : ‖Z * ((Real.exp A : ℂ) * D)‖ < ε / (C + 1) :=
    hsml Ec hE.2.1 Ef hE.1 s r hs hr
  have hn' : ‖p.incomingCuspNormalization L h Ec Ef‖ * Real.exp (-A) ≤ C := by
    simpa only [Ec, Ef, A, neg_div] using hn
  have he : Real.exp (-A) * Real.exp A = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  change ‖Z * (p.incomingCuspNormalization L h Ec Ef * D)‖ < ε
  calc
    _ = (‖p.incomingCuspNormalization L h Ec Ef‖ * Real.exp (-A)) *
        ‖Z * ((Real.exp A : ℂ) * D)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos A)]
      calc
        _ = (‖p.incomingCuspNormalization L h Ec Ef‖ * ‖Z‖ * ‖D‖) * 1 := by ring
        _ = _ := by rw [← he]; ring
    _ ≤ C * ‖Z * ((Real.exp A : ℂ) * D)‖ :=
      mul_le_mul_of_nonneg_right hn' (norm_nonneg _)
    _ < C * (ε / (C + 1)) := mul_lt_mul_of_pos_left heps hC
    _ < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (show 0 < C + 1 by linarith)).mpr
      nlinarith

end InfiniteZero.CuspParameters
