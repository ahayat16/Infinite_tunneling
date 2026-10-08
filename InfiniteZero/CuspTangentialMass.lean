import InfiniteZero.Construction
import InfiniteZero.LandauLaplaceUniformLeading
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The positive tangential coefficient of the incoming cusp pair

The fixed cutoff has mass between `s₀` and `2s₀`, because it equals one
on the central interval of length `s₀` and takes values in `[0,1]`.
The two real tangential integrals give its square. No claim about the
product or complex conjugation of the normal integrals is made here.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace InfiniteZero.CuspParameters

def cuspTangentialMass (p : CuspParameters) : ℝ :=
  ∫ s in Ioo (-p.s₀) p.s₀, p.χb s

theorem integrable_cuspTangentialCutoff {p : CuspParameters} (hp : p.BasicConditions) :
    Integrable p.χb :=
  hp.χb_smooth.continuous.integrable_of_hasCompactSupport hp.χb_support

theorem cuspTangentialMass_eq_integral {p : CuspParameters} (hp : p.BasicConditions) :
    p.cuspTangentialMass = ∫ s : ℝ, p.χb s := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hs
  exact image_eq_zero_of_notMem_tsupport (fun hmem => hs (hp.χb_localization hmem))

theorem cuspTangentialMass_bounds {p : CuspParameters} (hp : p.BasicConditions) :
    p.cuspTangentialMass ∈ Icc p.s₀ (2 * p.s₀) := by
  have hi := integrable_cuspTangentialCutoff hp
  have hcentral : (∫ s in Ioo (-p.s₀ / 2) (p.s₀ / 2), p.χb s) = p.s₀ := by
    calc
      _ = ∫ _s in Ioo (-p.s₀ / 2) (p.s₀ / 2), (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        exact hp.χb_one s ⟨hs.1.le, hs.2.le⟩
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [hp.s₀_pos])]
        simp only [smul_eq_mul, mul_one]
        ring
  constructor
  · rw [cuspTangentialMass_eq_integral hp, ← hcentral]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun s => (hp.χb_range s).1)
  · calc
      p.cuspTangentialMass ≤ ∫ _s in Ioo (-p.s₀) p.s₀, (1 : ℝ) :=
        setIntegral_mono_on hi.integrableOn
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioo (fun s _ => (hp.χb_range s).2)
      _ = 2 * p.s₀ := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [hp.s₀_pos])]
        simp only [smul_eq_mul, mul_one]
        ring

theorem cuspTangentialMass_pos {p : CuspParameters} (hp : p.BasicConditions) :
    0 < p.cuspTangentialMass :=
  hp.s₀_pos.trans_le (cuspTangentialMass_bounds hp).1

theorem integrable_cuspTangential_product {p : CuspParameters} (hp : p.BasicConditions) :
    Integrable (fun q : ℝ × ℝ => p.χb q.1 * p.χb q.2) (volume.prod volume) :=
  (integrable_cuspTangentialCutoff hp).mul_prod (integrable_cuspTangentialCutoff hp)

theorem integral_cuspTangential_product (p : CuspParameters) :
    (∫ q : ℝ × ℝ in Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀,
      p.χb q.1 * p.χb q.2 ∂volume.prod volume) = p.cuspTangentialMass ^ 2 := by
  rw [setIntegral_prod_mul]
  simp only [cuspTangentialMass, pow_two]

theorem integral_cuspTangential_iterated (p : CuspParameters) :
    (∫ s in Ioo (-p.s₀) p.s₀, ∫ r in Ioo (-p.s₀) p.s₀,
      p.χb s * p.χb r) = p.cuspTangentialMass ^ 2 := by
  simp only [integral_const_mul, integral_mul_const, cuspTangentialMass, pow_two]

theorem integral_cuspTangential_product_pos {p : CuspParameters} (hp : p.BasicConditions) :
    0 < ∫ q : ℝ × ℝ in Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀,
      p.χb q.1 * p.χb q.2 ∂volume.prod volume := by
  rw [integral_cuspTangential_product]
  exact sq_pos_of_pos (cuspTangentialMass_pos hp)

def activeTangentialLeadingCoefficient (p : CuspParameters) (L : ℝ) : ℝ :=
  landauLeadingCoefficient p.b 1 p.R ^ 2 *
    landauLeadingCoefficient p.b 1 (Geometry.activeDistance p.R L) *
      p.cuspTangentialMass ^ 2

/-- The real leading coefficient supplied by the three kernels and the
two tangential cutoffs is strictly positive. The sign of `sourcePairing`
and the complex normal saddle factors are separate quantities. -/
theorem activeTangentialLeadingCoefficient_pos {p : CuspParameters}
    (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    0 < p.activeTangentialLeadingCoefficient L := by
  have hR := landauLeadingCoefficient_pos hp.b_pos (by norm_num : (0 : ℝ) < 1) hp.radius_pos
  have hD := landauLeadingCoefficient_pos hp.b_pos (by norm_num : (0 : ℝ) < 1)
    (Geometry.activeDistance_pos hL)
  have hm := cuspTangentialMass_pos hp
  unfold activeTangentialLeadingCoefficient
  positivity

/-- The two source energies and the bridge energy remain distinct until
the limit. Their rates of convergence are immaterial for this coefficient. -/
theorem tendsto_activeTangentialLeadingCoefficient
    {ι : Type*} {l : Filter ι} {Ecore Efull : ι → ℝ}
    {p : CuspParameters} (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L)
    (hEcore : Tendsto Ecore l (𝓝 1)) (hEfull : Tendsto Efull l (𝓝 1)) :
    Tendsto (fun i => landauLeadingCoefficient p.b (Ecore i) p.R ^ 2 *
      landauLeadingCoefficient p.b (Efull i) (Geometry.activeDistance p.R L) *
        p.cuspTangentialMass ^ 2) l (𝓝 (p.activeTangentialLeadingCoefficient L)) := by
  have hcore := tendsto_landauLeadingCoefficient_parameters hp.b_pos
    (by norm_num : (0 : ℝ) < 1) hp.radius_pos hEcore
    (tendsto_const_nhds : Tendsto (fun _ : ι => p.R) l (𝓝 p.R))
  have hfull := tendsto_landauLeadingCoefficient_parameters hp.b_pos
    (by norm_num : (0 : ℝ) < 1) (Geometry.activeDistance_pos hL) hEfull
    (tendsto_const_nhds : Tendsto (fun _ : ι => Geometry.activeDistance p.R L) l
      (𝓝 (Geometry.activeDistance p.R L)))
  exact ((hcore.pow 2).mul hfull).mul_const (p.cuspTangentialMass ^ 2)

theorem tendsto_activeTangentialLeadingCoefficient_relative
    {ι : Type*} {l : Filter ι} {Ecore Efull : ι → ℝ}
    {p : CuspParameters} (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L)
    (hEcore : Tendsto Ecore l (𝓝 1)) (hEfull : Tendsto Efull l (𝓝 1)) :
    Tendsto (fun i => (landauLeadingCoefficient p.b (Ecore i) p.R ^ 2 *
      landauLeadingCoefficient p.b (Efull i) (Geometry.activeDistance p.R L) *
        p.cuspTangentialMass ^ 2) / p.activeTangentialLeadingCoefficient L) l (𝓝 1) := by
  simpa only [div_self (activeTangentialLeadingCoefficient_pos hp hL).ne'] using
    (tendsto_activeTangentialLeadingCoefficient hp hL hEcore hEfull).div_const
      (p.activeTangentialLeadingCoefficient L)

end InfiniteZero.CuspParameters
