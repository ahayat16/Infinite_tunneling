import InfiniteZero.CuspSourcePairingFubini
import InfiniteZero.NormalBoxTruncation
import InfiniteZero.CuspTangentialMass

/-!
# Integrating the real tangential parameters of the incoming cell

The normal integral is taken before either real tangential parameter.
Absolute integrability follows from the proved four-variable density
estimate on the coordinate rectangles. Uniform errors therefore integrate
with the exact tangential area, while the leading cutoff product integrates
to the square of its positive mass.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal

namespace InfiniteZero.CuspParameters

def incomingCuspNormalIntegral (p : CuspParameters)
    (L h Ecore Efull s r : ℝ) : ℂ :=
  ∫ q in positiveNormalBox p.t₀, p.incomingCuspDensity L h Ecore Efull q.1 q.2 s r

def incomingCuspIntegral (p : CuspParameters) (L h Ecore Efull : ℝ) : ℂ :=
  ∫ q in Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀,
    p.incomingCuspNormalIntegral L h Ecore Efull q.1 q.2

theorem integrableOn_incomingCuspNormalIntegral
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    IntegrableOn (fun q : ℝ × ℝ => p.incomingCuspNormalIntegral L h Ecore Efull q.1 q.2)
      (Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀) := by
  let μn : Measure (ℝ × ℝ) := volume.restrict (positiveNormalBox p.t₀)
  let μt : Measure (ℝ × ℝ) := volume.restrict
    (Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀)
  have hf : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      p.incomingCuspDensity L h Ecore Efull q.1.1 q.1.2 q.2.1 q.2.2) (μn.prod μt) := by
    simpa only [μn, μt, Measure.prod_restrict, ← Measure.volume_eq_prod,
      IntegrableOn, positiveNormalBox] using
      integrableOn_incomingCuspDensity_normalProduct hp hL hh hEc hEf
  exact hf.integral_prod_right

theorem incomingCuspIntegral_eq_tangents_first
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    p.incomingCuspIntegral L h Ecore Efull =
      ∫ s in Ioo (-p.s₀) p.s₀, ∫ r in Ioo (-p.s₀) p.s₀,
        ∫ t in Ioo 0 p.t₀, ∫ u in Ioo 0 p.t₀,
          p.incomingCuspDensity L h Ecore Efull t u s r := by
  have hi := integrableOn_incomingCuspNormalIntegral hp hL hh hEc hEf
  have houter : p.incomingCuspIntegral L h Ecore Efull =
      ∫ s in Ioo (-p.s₀) p.s₀, ∫ r in Ioo (-p.s₀) p.s₀,
        p.incomingCuspNormalIntegral L h Ecore Efull s r := by
    simpa only [incomingCuspIntegral, ← Measure.volume_eq_prod] using
      setIntegral_prod (fun q : ℝ × ℝ => p.incomingCuspNormalIntegral L h Ecore Efull q.1 q.2)
        (by simpa only [← Measure.volume_eq_prod] using hi)
  rw [houter]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hn := integrableOn_incomingCuspDensity_normals hp hL hh hEc hEf
    ⟨hs.1.le, hs.2.le⟩ ⟨hr.1.le, hr.2.le⟩
  simpa only [incomingCuspNormalIntegral, positiveNormalBox, ← Measure.volume_eq_prod] using
    setIntegral_prod (fun q : ℝ × ℝ => p.incomingCuspDensity L h Ecore Efull q.1 q.2 s r)
      (by simpa only [← Measure.volume_eq_prod] using hn)

theorem incomingCuspIntegral_eq_chart_integral
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    p.incomingCuspIntegral L h Ecore Efull =
      ∫ q in p.cuspChartDomain, ∫ r in p.cuspChartDomain,
        p.incomingCuspDensity L h Ecore Efull q.1 r.1 q.2 r.2 := by
  rw [incomingCuspIntegral_eq_tangents_first hp hL hh hEc hEf,
    incomingCuspDensity_integral_eq_tangents_first hp hL hh hEc hEf]

theorem incomingCuspIntegral_eq_chart_product_integral
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    p.incomingCuspIntegral L h Ecore Efull =
      ∫ q in p.cuspChartDomain ×ˢ p.cuspChartDomain,
        p.incomingCuspDensity L h Ecore Efull q.1.1 q.2.1 q.1.2 q.2.2 := by
  rw [incomingCuspIntegral_eq_chart_integral hp hL hh hEc hEf]
  symm
  simpa only [← Measure.volume_eq_prod] using
    setIntegral_prod (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      p.incomingCuspDensity L h Ecore Efull q.1.1 q.2.1 q.1.2 q.2.2)
      (by simpa only [← Measure.volume_eq_prod] using
        integrableOn_incomingCuspDensity_chartProduct hp hL hh hEc hEf)

theorem incoming_sourceCell_eq_incomingCuspIntegral
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull)
    (c Γ : ℝ) (φ : Wavefunction) (hφ : Continuous φ)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h Ecore ‖x‖ : ℂ)) :
    sourceCell p L h Efull (fun x => (c : ℂ) * φ x) 1 2 =
      -((h ^ 2 : ℝ) : ℂ) *
        (((h ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        p.incomingCuspIntegral L h Ecore Efull := by
  rw [incoming_sourceCell_eq_tangents_first hp hL hh hEc hEf c Γ φ hφ htail,
    incomingCuspIntegral_eq_tangents_first hp hL hh hEc hEf]

/-- A uniform complex error on the tangent rectangle integrates with its
exact area. Integrability of the physical density is proved, not assumed. -/
theorem norm_incomingCuspIntegral_sub_tangential_le
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull)
    (Z a : ℂ) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hbound : ∀ s ∈ Ioo (-p.s₀) p.s₀, ∀ r ∈ Ioo (-p.s₀) p.s₀,
      ‖Z * p.incomingCuspNormalIntegral L h Ecore Efull s r -
        a * (p.χb s * p.χb r : ℝ)‖ ≤ δ) :
    ‖Z * p.incomingCuspIntegral L h Ecore Efull - a * (p.cuspTangentialMass ^ 2 : ℝ)‖ ≤
      δ * (2 * p.s₀) ^ 2 := by
  have hi := integrableOn_incomingCuspNormalIntegral hp hL hh hEc hEf
  have hb : IntegrableOn (fun q : ℝ × ℝ => ((p.χb q.1 * p.χb q.2 : ℝ) : ℂ))
      (Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀) := by
    have hb' : IntegrableOn (fun q : ℝ × ℝ => ((p.χb q.1 * p.χb q.2 : ℝ) : ℂ))
        (Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀) (volume.prod volume) :=
      (integrable_cuspTangential_product hp).ofReal.integrableOn
    simpa only [← Measure.volume_eq_prod] using hb'
  have hmass : (∫ q : ℝ × ℝ in Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀,
      p.χb q.1 * p.χb q.2) = p.cuspTangentialMass ^ 2 := by
    simpa only [← Measure.volume_eq_prod] using integral_cuspTangential_product p
  have heq : Z * p.incomingCuspIntegral L h Ecore Efull -
      a * (p.cuspTangentialMass ^ 2 : ℝ) =
      ∫ q in Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀,
        Z * p.incomingCuspNormalIntegral L h Ecore Efull q.1 q.2 -
          a * (p.χb q.1 * p.χb q.2 : ℝ) := by
    rw [integral_sub (hi.const_mul Z) (hb.const_mul a), integral_const_mul,
      integral_const_mul, integral_complex_ofReal, hmass]
    rfl
  have hfinite : volume (Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀) < ∞ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have harea : volume.real (Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀) = (2 * p.s₀) ^ 2 := by
    rw [Measure.volume_eq_prod, measureReal_prod_prod,
      Real.volume_real_Ioo_of_le (by linarith [hp.s₀_pos])]
    ring
  rw [heq, ← harea]
  exact norm_setIntegral_le_of_norm_le_const hfinite
    (fun q hq => hbound q.1 hq.1 q.2 hq.2)

end InfiniteZero.CuspParameters
