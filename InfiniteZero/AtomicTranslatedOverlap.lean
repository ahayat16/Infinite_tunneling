import InfiniteZero.MagneticOverlapTail
import InfiniteZero.AtomicGroundAgmon
import InfiniteZero.OverlapDecayScalar

/-!
# Uniform overlap control for every normalized full atomic ground state

The Agmon estimate is uniform in the ground-state representative. Applying
the geometric overlap bound before making any phase choice gives the same
separation-independent threshold for every normalized full atomic state.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace InfiniteZero.CuspParameters

theorem exists_translatedOverlap_bound_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ d > 0, ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ∀ L : ℝ, 4 * p.r₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
        |translatedOverlap p.b L coupling φ| ≤ C / coupling * Real.exp (-d * coupling) := by
  obtain ⟨C, hC, d, hd, T, hT, htail⟩ :=
    exists_atomicGround_agmon_tail_of_radialData hp hRad hAcore hApot
  refine ⟨2 * Real.sqrt C, mul_pos (by norm_num) (Real.sqrt_pos.mpr hC), d, hd, T, hT, ?_⟩
  intro coupling hc L hL φ hφ
  have hmass := (htail coupling hc).2.1 φ hφ
  have hgeom := norm_waveInner_leftState_rightState_sq_le_tail p.b coupling
    (show 0 < 4 * p.r₀ by linarith [hp.r₀_pos]) hL hφ.1.2.1 hφ.2
  have hs := hgeom.trans (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 4))
  apply (Complex.abs_re_le_norm _).trans
  simpa only [abs_of_nonneg (norm_nonneg _)] using
    le_overlap_decay_of_sq_le (hT.trans_le hc) hC.le hs

theorem exists_translatedOverlap_uniform_small_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling → ∀ L : ℝ, 4 * p.r₀ ≤ L →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.potential coupling φ →
        |translatedOverlap p.b L coupling φ| < ε := by
  obtain ⟨C, _, d, hd, T, hT, hbound⟩ :=
    exists_translatedOverlap_bound_of_radialData hp hRad hAcore hApot
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_overlap_decay C hd).eventually (Iio_mem_nhds hε))
  refine ⟨max T N, hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc L hL φ hφ
  exact (hbound coupling ((le_max_left _ _).trans hc) L hL φ hφ).trans_lt
    (hN coupling ((le_max_right _ _).trans hc))

end InfiniteZero.CuspParameters
