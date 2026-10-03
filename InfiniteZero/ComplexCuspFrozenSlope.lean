import InfiniteZero.ActiveSaddleSlopeEnergy
import InfiniteZero.LogFlatActiveWindow

/-!
# Uniformly freezing the complex normal slope on the actual active window

An O(h) slope error times two normal coordinates of size O(h^(3/4)),
divided by h, tends to zero uniformly. The last theorem supplies the O(h)
bound from the actual core and full atomic energies, not as an assumption.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero

def complexSlopeFreezingFactor (cstar c : ℂ) (h : ℝ) (t u : ℂ) : ℂ :=
  Complex.exp ((cstar - c) * (t + u) / (h : ℂ))

theorem norm_slopeFreezingExponent_le {cstar c t u : ℂ} {h B M tStar : ℝ}
    (hh : 0 < h) (hB : 0 ≤ B) (_hM : 0 ≤ M) (htStar : 0 < tStar)
    (hc : ‖c - cstar‖ ≤ B * h)
    (ht : ‖t‖ ≤ M * logFlatActiveWindow tStar h)
    (hu : ‖u‖ ≤ M * logFlatActiveWindow tStar h) :
    ‖(cstar - c) * (t + u) / (h : ℂ)‖ ≤ 2 * B * M * logFlatActiveWindow tStar h := by
  have hw := (logFlatActiveWindow_pos htStar h).le
  have htu : ‖t + u‖ ≤ 2 * M * logFlatActiveWindow tStar h := by
    linarith [norm_add_le t u]
  rw [norm_div, norm_mul, norm_sub_rev cstar c, Complex.norm_real,
    Real.norm_of_nonneg hh.le]
  calc
    _ ≤ (B * h) * (2 * M * logFlatActiveWindow tStar h) / h := by gcongr
    _ = _ := by field_simp

theorem eventually_complexSlopeFreezingFactor_uniform
    {c : ℝ → ℂ} {cstar : ℂ} {B M tStar : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (htStar : 0 < tStar)
    (hc : ∀ᶠ h : ℝ in 𝓝[>] 0, ‖c h - cstar‖ ≤ B * h)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ t u : ℂ,
      ‖t‖ ≤ M * logFlatActiveWindow tStar h →
      ‖u‖ ≤ M * logFlatActiveWindow tStar h →
      ‖complexSlopeFreezingFactor cstar (c h) h t u - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
    (Complex.continuous_exp.continuousAt : ContinuousAt Complex.exp (0 : ℂ)) ε hε
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,
      2 * B * M * logFlatActiveWindow tStar h < δ := by
    have hz : Tendsto (fun h : ℝ => 2 * B * M * logFlatActiveWindow tStar h)
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_logFlatActiveWindow tStar).const_mul (2 * B * M)
    exact hz.eventually (gt_mem_nhds hδ)
  filter_upwards [hc, hsmall, self_mem_nhdsWithin] with h hch hsh hh
  intro t u ht hu
  have hn := norm_slopeFreezingExponent_le hh hB hM htStar hch ht hu
  have hd : dist ((cstar - c h) * (t + u) / (h : ℂ)) 0 < δ := by
    simpa only [dist_zero_right] using hn.trans_lt hsh
  simpa only [complexSlopeFreezingFactor, dist_eq_norm, Complex.exp_zero] using hclose hd

namespace CuspParameters

theorem eventually_atomic_slopeFreezingFactor_uniform_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (L : ℝ) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ t u : ℂ,
      ‖t‖ ≤ M * logFlatActiveWindow p.tStar h →
      ‖u‖ ≤ M * logFlatActiveWindow p.tStar h →
      ‖complexSlopeFreezingFactor (p.activeSaddleSlope L)
        (p.movingActiveSaddleSlope L
          (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
          (scaledAtomicEnergy p h⁻¹)) h t u - 1‖ < ε := by
  obtain ⟨T, _hT, hbound⟩ :=
    exists_activeSaddleSlope_energy_bound_of_radialData hp hRad hAcore hApot L
  have hs : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖p.movingActiveSaddleSlope L
        (-(h ^ 2 * atomicGroundEnergy p.b p.core h⁻¹))
        (scaledAtomicEnergy p h⁻¹) - p.activeSaddleSlope L‖ ≤ hRad.energyBound * h := by
    filter_upwards [tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop T)] with h hh
    simpa only [inv_inv, div_inv_eq_mul] using hbound h⁻¹ hh
  exact eventually_complexSlopeFreezingFactor_uniform hRad.energyBound_pos.le hM
    (hp.t₀_pos.trans hp.t₀_lt) hs hε

end CuspParameters
end InfiniteZero
