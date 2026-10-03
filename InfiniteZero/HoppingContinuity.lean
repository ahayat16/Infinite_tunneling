import InfiniteZero.AtomicGroundDilationComparison
import InfiniteZero.ParityTrialStates
import InfiniteZero.MagneticWeightedGraph
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of the actual canonical hopping

The hopping is a bounded quadratic expression on normalized physical L²
states. A fixed reference state pulled back by dilation has a continuous
hopping because the potential fixes a compact integration region. Actual
ground states approach this reference up to a unit phase, which cancels
exactly from the hopping. No continuous canonical phase is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace InfiniteZero

private theorem norm_toLp_eq_sqrt_mass {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    ‖hφ.toLp φ‖ = Real.sqrt (mass φ) := by
  rw [← norm_toLp_sq_eq_mass hφ, Real.sqrt_sq (norm_nonneg _)]

private theorem integrable_potential_pair {φ ψ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    {V : Potential} (hV : Continuous V) {B : ℝ} (hbound : ∀ x, |V x| ≤ B) :
    Integrable (fun x => star (φ x) * (V x : ℂ) * ψ x) := by
  have h := hφ.star.integrable_mul (memLp_boundedPotential_mul V hV hbound hψ)
  convert h using 1
  ext x
  change star (φ x) * (V x : ℂ) * ψ x = star (φ x) * ((V x : ℂ) * ψ x)
  ring

private theorem norm_integral_potential_pair_le {φ ψ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    {V : Potential} (hV : Continuous V) {B : ℝ} (hbound : ∀ x, |V x| ≤ B) :
    ‖∫ x, star (φ x) * (V x : ℂ) * ψ x‖ ≤
      B * Real.sqrt (mass φ) * Real.sqrt (mass ψ) := by
  let Bop := boundedPotentialMul V hV hbound
  have hrep := (represents_toLp hψ).boundedPotentialMul V hV hbound
  have hi := (represents_toLp hφ).inner_eq_waveInner hrep
  have heq : (∫ x, star (φ x) * (V x : ℂ) * ψ x) =
      inner ℂ (hφ.toLp φ) (Bop (hψ.toLp ψ)) := by
    rw [hi]
    unfold waveInner
    congr 1
    ext x
    ring
  rw [heq]
  calc
    _ ≤ ‖hφ.toLp φ‖ * ‖Bop (hψ.toLp ψ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖hφ.toLp φ‖ * (B * ‖hψ.toLp ψ‖) :=
      mul_le_mul_of_nonneg_left (norm_boundedPotentialMul_apply_le V hV hbound _) (norm_nonneg _)
    _ = _ := by rw [norm_toLp_eq_sqrt_mass hφ, norm_toLp_eq_sqrt_mass hψ]; ring

/-- A bilinear continuity bound for the physical hopping, on arbitrary normalized L² states. -/
theorem norm_hopping_sub_le_of_mass_one
    (b L coupling : ℝ) {V : Potential} (hV : Continuous V)
    {B : ℝ} (hbound : ∀ x, |V x| ≤ B)
    {φ ψ : Wavefunction} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (hmφ : mass φ = 1) (hmψ : mass ψ = 1) :
    ‖hopping b V L coupling φ - hopping b V L coupling ψ‖ ≤
      2 * coupling ^ 2 * B * Real.sqrt (mass (φ - ψ)) := by
  let Vleft : Potential := fun x => V (x + displacement L)
  have hVc : Continuous Vleft := hV.comp (continuous_id.add continuous_const)
  have hVb (x : Plane) : |Vleft x| ≤ B := hbound _
  let F := leftState b L coupling φ
  let G := leftState b L coupling ψ
  let P := rightState b L coupling φ
  let Q := rightState b L coupling ψ
  have hF : MemLp F 2 volume := memLp_leftState b L coupling hφ
  have hG : MemLp G 2 volume := memLp_leftState b L coupling hψ
  have hP : MemLp P 2 volume := memLp_rightState b L coupling hφ
  have hQ : MemLp Q 2 volume := memLp_rightState b L coupling hψ
  have hleft : F - G = leftState b L coupling (φ - ψ) := by
    ext x
    simp only [F, G, leftState, magneticTranslation, Pi.sub_apply, mul_sub]
  have hright : P - Q = rightState b L coupling (φ - ψ) := by
    ext x
    simp only [P, Q, rightState, leftState, magneticTranslation, Pi.sub_apply, mul_sub]
  have hsplit :
      (∫ x, star (F x) * (Vleft x : ℂ) * P x) -
        (∫ x, star (G x) * (Vleft x : ℂ) * Q x) =
      (∫ x, star ((F - G) x) * (Vleft x : ℂ) * P x) +
        (∫ x, star (G x) * (Vleft x : ℂ) * ((P - Q) x)) := by
    rw [← integral_sub (integrable_potential_pair hF hP hVc hVb)
      (integrable_potential_pair hG hQ hVc hVb),
      ← integral_add (integrable_potential_pair (hF.sub hG) hP hVc hVb)
        (integrable_potential_pair hG (hP.sub hQ) hVc hVb)]
    congr 1
    ext x
    simp only [Pi.sub_apply, star_sub]
    ring
  have hn : ‖(∫ x, star (F x) * (Vleft x : ℂ) * P x) -
        (∫ x, star (G x) * (Vleft x : ℂ) * Q x)‖ ≤
      2 * B * Real.sqrt (mass (φ - ψ)) := by
    rw [hsplit]
    have hh := (norm_add_le _ _).trans (add_le_add
      (norm_integral_potential_pair_le (hF.sub hG) hP hVc hVb)
      (norm_integral_potential_pair_le hG (hP.sub hQ) hVc hVb))
    have hmFG : mass (F - G) = mass (φ - ψ) := by rw [hleft, mass_leftState]
    have hmPQ : mass (P - Q) = mass (φ - ψ) := by rw [hright, mass_rightState]
    have hmP : mass P = 1 := (mass_rightState b L coupling φ).trans hmφ
    have hmG : mass G = 1 := (mass_leftState b L coupling ψ).trans hmψ
    rw [hmFG, hmPQ, hmP, hmG, Real.sqrt_one, mul_one, mul_one] at hh
    convert hh using 1
    ring
  unfold hopping
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg coupling)]
  have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg coupling)
  convert hh using 1
  ring

/-- A fixed continuous reference state, pulled back by dilation, gives a continuous hopping. -/
theorem continuous_hopping_magneticDilation_inv
    (b L : ℝ) {V : Potential} (hV : Continuous V) (hcompact : HasCompactSupport V)
    {φ : Wavefunction} (hφ : Continuous φ) :
    Continuous (fun coupling : ℝ => hopping b V L coupling (magneticDilation coupling⁻¹ φ)) := by
  let F : ℝ → Plane → ℂ := fun coupling x =>
    star (leftState b L coupling (magneticDilation coupling⁻¹ φ) x) *
      (V (x + displacement L) : ℂ) *
        rightState b L coupling (magneticDilation coupling⁻¹ φ) x
  have hF : Continuous F.uncurry := by
    dsimp only [F, Function.uncurry_def, leftState, rightState, magneticTranslation]
    simp only [magneticDilation_apply, Real.sqrt_inv, Complex.ofReal_inv, inv_inv]
    unfold wedge
    apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.star
        apply Continuous.mul
        · fun_prop
        · apply Continuous.mul
          · fun_prop
          · exact hφ.comp (by fun_prop)
      · exact Complex.continuous_ofReal.comp (hV.comp (by fun_prop))
    · apply Continuous.mul
      · fun_prop
      · apply Continuous.mul
        · fun_prop
        · exact hφ.comp (by fun_prop)
  have hcomp : HasCompactSupport (fun x : Plane => V (x + displacement L)) :=
    hcompact.comp_homeomorph (Homeomorph.addRight (displacement L))
  have hI : Continuous (fun coupling : ℝ => ∫ x : Plane, F coupling x) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support hcomp hF.continuousOn
    intro coupling x _ hx
    have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [F, hz, Complex.ofReal_zero, mul_zero, zero_mul]
  simpa only [hopping, F] using
    (Complex.continuous_ofReal.comp (continuous_id.pow 2)).mul hI

namespace CuspParameters

/-- Continuity of the actual canonical hopping follows without a continuous ground-state choice. -/
theorem exists_canonicalHopping_continuous_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ L : ℝ,
      ContinuousOn (canonicalHopping p.b p.potential L) (Ici T) := by
  obtain ⟨C, hC, Tc, hTc, hcomparison⟩ :=
    exists_atomicGround_phase_dilation_comparison_of_radialData hp hRad hAcore hApot
  obtain ⟨Tg, hTg, hground⟩ :=
    eventual_atomicGround_properties_of_radialData hp hRad hAcore hApot
  let T := max Tc Tg
  have hT : 0 < T := hTc.trans_le (le_max_left _ _)
  have hspec (coupling : ℝ) (hc : T ≤ coupling) :
      IsAtomicGroundState p.b p.potential coupling
        (canonicalAtomicState p.b p.potential coupling) :=
    canonicalAtomicState_spec _ _ _ ((hground coupling ((le_max_right _ _).trans hc)).1)
  have hVb (x : Plane) : |p.potential x| ≤ 1 :=
    abs_le.mpr ⟨(potential_range hp x).1, (potential_range hp x).2.trans zero_le_one⟩
  refine ⟨T, hT, ?_⟩
  intro L μ hμ
  have hμpos : 0 < μ := hT.trans_le hμ
  let φμ := canonicalAtomicState p.b p.potential μ
  have hφμ : IsAtomicGroundState p.b p.potential μ φμ := hspec μ hμ
  let ρ : ℝ → Wavefunction := fun coupling =>
    magneticDilation coupling⁻¹ (magneticDilation μ φμ)
  let Href : ℝ → ℂ := fun coupling => hopping p.b p.potential L coupling (ρ coupling)
  have href : Continuous Href := continuous_hopping_magneticDilation_inv p.b L
    (potential_contDiff hp).continuous (potential_hasCompactSupport hp)
    (contDiff_magneticDilation μ hφμ.1.1).continuous
  have hrefμ : Href μ = canonicalHopping p.b p.potential L μ := by
    dsimp only [Href, ρ]
    rw [magneticDilation_inv_cancel hμpos]
    rfl
  have hbound (coupling : ℝ) (hc : T ≤ coupling) :
      ‖canonicalHopping p.b p.potential L coupling - Href coupling‖ ≤
        2 * coupling ^ 2 * Real.sqrt (C * |coupling - μ|) := by
    have hcpos : 0 < coupling := hT.trans_le hc
    let φ := canonicalAtomicState p.b p.potential coupling
    have hφ : IsAtomicGroundState p.b p.potential coupling φ := hspec coupling hc
    have hρ : MemLp (ρ coupling) 2 volume :=
      (hφμ.1.2.1.magneticDilation hμpos).magneticDilation (inv_pos.mpr hcpos)
    have hmρ : mass (ρ coupling) = 1 := by
      dsimp only [ρ]
      rw [mass_magneticDilation (inv_pos.mpr hcpos), mass_magneticDilation hμpos, hφμ.2]
    obtain ⟨z, hz, hclose⟩ := hcomparison coupling μ
      ((le_max_left _ _).trans hc) ((le_max_left _ _).trans hμ) φ φμ hφ hφμ
    have hmz : mass (z • ρ coupling) = 1 := by
      rw [mass_smul_wavefunction, hz, hmρ]
      norm_num
    have hh := norm_hopping_sub_le_of_mass_one p.b L coupling
      (potential_contDiff hp).continuous hVb hφ.1.2.1 (hρ.const_smul z) hφ.2 hmz
    rw [hopping_smul_unit p.b p.potential L coupling z hz] at hh
    simp only [mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hclose)
      (mul_nonneg (by norm_num) (sq_nonneg coupling)))
  have hmajor : Tendsto (fun coupling : ℝ =>
      2 * coupling ^ 2 * Real.sqrt (C * |coupling - μ|)) (𝓝[Ici T] μ) (𝓝 0) := by
    have hh : Continuous (fun coupling : ℝ =>
        2 * coupling ^ 2 * Real.sqrt (C * |coupling - μ|)) := by fun_prop
    simpa only [sub_self, abs_zero, mul_zero, Real.sqrt_zero] using
      ((hh.tendsto μ).mono_left nhdsWithin_le_nhds)
  have hdiff : Tendsto
      (fun coupling : ℝ => canonicalHopping p.b p.potential L coupling - Href coupling)
      (𝓝[Ici T] μ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hmajor
    filter_upwards [self_mem_nhdsWithin] with coupling hc
    exact hbound coupling hc
  have hh := hdiff.add (href.continuousAt.continuousWithinAt : ContinuousWithinAt Href (Ici T) μ)
  simpa only [sub_add_cancel, zero_add, hrefμ] using hh

end CuspParameters
end InfiniteZero
