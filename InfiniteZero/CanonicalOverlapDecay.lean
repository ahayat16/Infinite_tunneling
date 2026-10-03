import InfiniteZero.MagneticOverlapTail
import InfiniteZero.AtomicGroundAgmon
import InfiniteZero.OverlapDecayScalar
import InfiniteZero.ParityTransfer

/-!
# Exponential smallness of the actual canonical double-well overlap

The geometric overlap estimate is applied to the actual normalized atomic
ground state and its proved exterior Agmon mass. Constants and the coupling
threshold are chosen before every separation L >= 4 r0.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology

namespace InfiniteZero.CuspParameters

theorem exists_canonical_translated_overlap_bound_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ L : ℝ, 4 * p.r₀ ≤ L →
        ‖waveInner (leftState p.b L coupling (canonicalAtomicState p.b p.potential coupling))
          (rightState p.b L coupling (canonicalAtomicState p.b p.potential coupling))‖ ≤
          C / coupling * Real.exp (-d * coupling) := by
  obtain ⟨C, hC, d, hd, T, hT, htail⟩ :=
    exists_canonicalAtomicState_agmon_tail_of_radialData hp hRad hAcore hApot
  refine ⟨2 * Real.sqrt C, mul_pos (by norm_num) (Real.sqrt_pos.mpr hC), d, hd, T, hT, ?_⟩
  intro coupling hc L hL
  obtain ⟨hφ, hmass⟩ := htail coupling hc
  have hgeom := norm_waveInner_leftState_rightState_sq_le_tail p.b coupling
    (show 0 < 4 * p.r₀ by linarith [hp.r₀_pos]) hL hφ.1.2.1 hφ.2
  have hs := hgeom.trans (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 4))
  simpa only [abs_of_nonneg (norm_nonneg _)] using
    le_overlap_decay_of_sq_le (hT.trans_le hc) hC.le hs

theorem exists_canonicalOverlap_bound_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ L : ℝ, 4 * p.r₀ ≤ L →
        |canonicalOverlap p.b p.potential L coupling| ≤
          C / coupling * Real.exp (-d * coupling) := by
  obtain ⟨C, hC, d, hd, T, hT, hbound⟩ :=
    exists_canonical_translated_overlap_bound_of_radialData hp hRad hAcore hApot
  refine ⟨C, hC, d, hd, T, hT, ?_⟩
  intro coupling hc L hL
  exact (Complex.abs_re_le_norm _).trans (hbound coupling hc L hL)

/-- In particular, this supplies the physical overlap limit required by
the later parity Schur transfer. No double-well spectral data are assumed. -/
theorem tendsto_canonicalOverlap_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {L : ℝ} (hL : 4 * p.r₀ ≤ L) :
    Tendsto (canonicalOverlap p.b p.potential L) atTop (𝓝 0) := by
  obtain ⟨C, _hC, d, hd, T, _hT, hbound⟩ :=
    exists_canonicalOverlap_bound_of_radialData hp hRad hAcore hApot
  apply squeeze_zero_norm' _ (tendsto_overlap_decay C hd)
  filter_upwards [eventually_ge_atTop T] with coupling hc
  simpa only [Real.norm_eq_abs] using hbound coupling hc L hL

/-- Uniform smallness precedes the choice of separation. -/
theorem exists_canonicalOverlap_uniform_small_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, 4 * p.r₀ ≤ L →
      |canonicalOverlap p.b p.potential L coupling| < ε := by
  obtain ⟨C, _hC, d, hd, T, hT, hbound⟩ :=
    exists_canonicalOverlap_bound_of_radialData hp hRad hAcore hApot
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_overlap_decay C hd).eventually (Iio_mem_nhds hε))
  refine ⟨max T N, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL
  exact (hbound coupling ((le_max_left _ _).trans hc) L hL).trans_lt
    (hN coupling ((le_max_right _ _).trans hc))

end InfiniteZero.CuspParameters
